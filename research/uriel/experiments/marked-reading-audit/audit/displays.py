"""Reconstruct the experiment from archived user-visible prompts without importing the runner."""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ARMS = ('unmarked', 'marked', 'filtered')
SEED = 2026112449
MODEL = 'gpt-oss:20b'
DIGEST = '17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7'
HEADER = re.compile(r'^mark ID stu target_current initial (M\d+) (M\d+) target_current_above_threshold$')
OBS = re.compile(r'^Observed readings: initial = ([LH]); (M\d+) = ([LH])\.$')
CLAIM = re.compile(r'^Question: is the signed current of (R\d+) > (-?\d+(?:/\d+)?) A\?$')
ROW = re.compile(r'^\. ([A-Z]{2}) ([01]{3}) (-?\d+(?:/\d+)?) ([LH]) ([LH]) ([LH]) ([YN])$')


def check(test, error):
    if not test:
        raise ValueError(error)


def exactly_one(pattern, lines, name):
    matched = [(i, m.groups()) for i, line in enumerate(lines) if (m := pattern.fullmatch(line.rstrip('\n')))]
    check(len(matched) == 1, name)
    return matched[0]


def read_json(path):
    return json.loads(path.read_bytes())


def audit_triple(texts, truth):
    lines = texts['unmarked'].splitlines(keepends=True)
    head, meters = exactly_one(HEADER, lines, 'invalid table header')
    _, (initial, meter, reading) = exactly_one(OBS, lines, 'invalid printed observations')
    _, (target, threshold) = exactly_one(CLAIM, lines, 'invalid printed target')
    check((initial, meter, reading) == (truth['initial_reading'], truth['meter'], truth['reading']), 'observations differ from physical case')
    check(target == truth['signed_branch'] and threshold == truth['target_threshold'], 'claim differs from physical case')
    check(len(set(meters)) == 2 and set(meters) == set(truth['menu']) and meter in meters, 'meter list changed')
    check(lines[0].rstrip('\n') == truth['description'], 'circuit description differs')
    check('Initial comparator: '+truth['initial_description']+'\n' in lines, 'initial calibration differs')
    check('Other comparators: '+' | '.join(f'{m}: {truth["menu"][m]}' for m in meters)+'\n' in lines, 'meter definitions differ')
    states = {}
    second_col = meters.index(meter)
    row_lines = {}
    for i, line in enumerate(lines[head+1:head+9], head+1):
        match = ROW.fullmatch(line.rstrip('\n'))
        check(match is not None, 'invalid public row')
        sid, bits, current, first, comparator_a, comparator_b, sign = match.groups()
        labels = (comparator_a, comparator_b)
        physical = truth['states'].get(sid)
        check(physical is not None and sid not in states, 'unknown or repeated public ID')
        check((bits, current, first) == (physical['bits'], physical['target_current'], physical['initial']), 'public electrical values differ')
        check(dict(zip(meters,labels)) == physical['obs'], 'printed meter state differs')
        above = Fraction(current) > Fraction(threshold)
        check((sign == 'Y') == above == physical['answer'], 'printed truth differs from strict current threshold')
        states[sid] = (bits, first, labels[second_col], sign)
        row_lines[i] = sid
    check(list(states)==truth['state_order'] and len({v[0] for v in states.values()})==8, 'wrong row order or switch assignments')
    check(lines[head+9:head+10]==['\n'] and sum(line.startswith(('. ', '* ')) for line in lines)==8, 'unexpected calibration rows')
    first_set = {i for i, (_,x,_,_) in states.items() if x == initial}
    second_set = {i for i, (_,_,x,_) in states.items() if x == reading}
    live = first_set & second_set
    for pool in (first_set, second_set):
        check(len(pool)==4 and {states[i][3] for i in pool}=={'N','Y'}, 'one-lamp shortcut')
    check(len(live)==2 and set(truth['survivors'])==live and set(truth['eligible'])==first_set, 'wrong jointly compatible settings')
    signs = {states[i][3] for i in live}
    verdict = 'U' if len(signs)==2 else next(iter(signs))
    kind = 'ambiguous' if verdict=='U' else 'decisive'
    check(kind==truth['kind'], 'wrong printed verdict stratum')
    expected_marked = ''.join('*'+line[1:] if row_lines.get(i) in live else line for i,line in enumerate(lines))
    check(texts['marked'] == expected_marked, 'mark differs from the two compatible rows')
    check(len(expected_marked)==len(texts['unmarked']) and
          sum(a!=b for a,b in zip(expected_marked,texts['unmarked']))==2, 'not exactly two single-character changes')
    expected_filtered = ''.join(line for i,line in enumerate(lines) if i not in row_lines or row_lines[i] in live)
    check(texts['filtered'] == expected_filtered, 'filtered view differs from removing six incompatible rows')
    return dict(kind=kind, reading=reading, meter=meter, initial_value=initial, verdict=verdict, family=truth['family'],
                initial_only=sorted(first_set), second_only=sorted(second_set), joint=sorted(live),
                schema_order=sorted(states,key=lambda i:states[i][0]),
                target_yes=sorted(i for i, s in states.items() if s[3]=='Y'))


def payload(system, user, ids, seed):
    return {'model':MODEL, 'messages':[{'role':'system','content':system},{'role':'user','content':user}],
            'keep_alive':'9m','stream':False,'think':'low',
            'options':{'temperature':0, 'seed':seed,'num_predict':2048,'num_ctx':8192},
            'format':{'type':'object','additionalProperties':False,'required':['verdict','certificate'],
                      'properties':{'verdict':{'type':'string','enum':['Y','N','U']},
                                    'certificate':{'type':'array','minItems':1,'maxItems':8,
                                                   'items':{'type':'string','enum':ids}}}}}


def request_hash(request):
    return sha256(json.dumps(request,sort_keys=True).encode('utf-8')).hexdigest()


def match_hash(req, digest):
    check(request_hash(req)==digest, 'request differs from locked reconstruction')


def audit_schedule(jobs, cases):
    check(len(jobs)==72, 'session count')
    orders=defaultdict(list)
    for start in range(0,72,24):
        wave=jobs[start:start+24]
        check({j['record'] for j in wave}==set(cases) and Counter(j['arm'] for j in wave)==dict.fromkeys(ARMS,8), 'unbalanced wave')
        for j in wave:
            orders[j['record']].append(j['arm'])
    patterns = defaultdict(Counter)
    for rid, seq in orders.items():
        check(set(seq)==set(ARMS), 'incomplete triple')
        case=cases[rid]
        patterns[case['kind'],case['reading']][tuple(seq)]+=1
    expected=Counter(permutations(ARMS))
    check(len(patterns)==4 and all(v==expected for v in patterns.values()), 'unbalanced permutations by stratum')
    return {k+'_'+s:{'/'.join(seq):v for seq,v in sorted(c.items())} for (k,s),c in sorted(patterns.items())}


def rejected(f, expected):
    try:
        f()
    except ValueError as e:
        check(str(e)==expected,'mutation detected by unexpected check: '+str(e))
    else:
        raise ValueError('corruption escaped: '+expected)


def mutation_controls(texts, truth, case, template, jobs, cases):
    bad=texts.copy()
    lines=bad['marked'].splitlines(keepends=True)
    a=next(i for i,l in enumerate(lines) if l.startswith('* '))
    b=next(i for i,l in enumerate(lines) if l.startswith('. '))
    lines[a]='.'+lines[a][1:]
    lines[b]='*'+lines[b][1:]
    bad['marked']=''.join(lines)
    rejected(lambda:audit_triple(bad,truth), 'mark differs from the two compatible rows')

    bad=texts.copy()
    removed_one=next(l for l in bad['filtered'].splitlines(keepends=True) if l.startswith('. '))
    bad['filtered']=bad['filtered'].replace(removed_one,'',1)
    rejected(lambda:audit_triple(bad,truth), 'filtered view differs from removing six incompatible rows')

    digest=request_hash(template)
    malformed=deepcopy(template)
    malformed['format']['properties']['certificate']['items']['enum']=case['joint']
    rejected(lambda:match_hash(malformed,digest), 'request differs from locked reconstruction')
    # Exchange full exposure sequences within one position of the schedule across two strata.
    # Swapping arm names for all appearances of the two selected records would not preserve wave counts.
    # Swapping record IDs instead preserves both wave counts and unique triples, testing the finer balance rule.
    jobs2=deepcopy(jobs)
    rid0=jobs2[0]['record']
    seq0=[j['arm'] for j in jobs if j['record']==rid0]
    other=next(r for r in cases if (cases[r]['kind'],cases[r]['reading'])!=(cases[rid0]['kind'],cases[rid0]['reading'])
               and [j['arm'] for j in jobs if j['record']==r]!=seq0)
    for j in jobs2:
        j['record']={rid0:other, other:rid0}.get(j['record'],j['record'])
    rejected(lambda:audit_schedule(jobs2,cases),'unbalanced permutations by stratum')
    return ['wrong_survivor_mark_equal_number','one_genuine_filtered_survivor_missing',
            'grammar_restricted_to_two_ids','order_swap_preserving_wave_counts']


def run(root):
    pilot=root/'pilot'
    reg=read_json(pilot/'freeze.json')
    check(reg['model']=={'tag':MODEL,'digest':DIGEST,'max_tokens':2048,'think':'low'} and reg['ollama']=='0.40.18' and
          reg['seed']==SEED and reg['socket_timeout_seconds']==900 and reg['sessions']==reg['max_requests']==72 and
          reg['direct_paid_api_cap_usd']==0,'model, runtime, session or spend constraint differs')
    for name, digest in reg['sha256'].items():
        check(sha256((root/name).read_bytes()).hexdigest()==digest, 'frozen file changed: '+name)
    records=read_json(root/'circuits'/'records.json')
    jobs=read_json(pilot/'order.json')
    system=(pilot/'method.txt').read_bytes().decode('utf-8').strip()
    cases, hashes = {}, {}
    for n,(rid,row) in enumerate(sorted(records.items())):
        texts={a:(pilot/'prompts'/f'{rid}.{a}.txt').read_bytes().decode('utf-8') for a in ARMS}
        case=audit_triple(texts,row)
        cases[rid]=case
        hashes[rid]={}
        for arm in ARMS:
            p=payload(system,texts[arm],case['schema_order'],SEED+n)
            entries=[j for j in jobs if j['record']==rid and j['arm']==arm]
            check(len(entries)==1,'missing or duplicate record/display')
            match_hash(p,entries[0]['request_sha256'])
            hashes[rid][arm]=request_hash(p)
    permutations_by_slot=audit_schedule(jobs,cases)
    groups=defaultdict(list)
    for c in cases.values():
        groups[c['family']].append(c)
    check(len(groups)==6,'expected six layouts')
    for group in groups.values():
        check(len(group)==4 and len({tuple(c['initial_only']) for c in group})==1,'layout changed first observation')
        for k in ('decisive','ambiguous'):
            pair=[c for c in group if c['kind']==k]
            check(len(pair)==2 and len({c['meter'] for c in pair})==1 and {c['reading'] for c in pair}=={'H','L'},'changed twin design')
            check(set(pair[0]['joint']).isdisjoint(pair[1]['joint']), 'twins reuse witnesses')
            check({c['verdict'] for c in pair}==({'U'} if k=='ambiguous' else {'Y','N'}),'incorrect advertised counterfactual')
    polarity=Counter(c['verdict'] for c in cases.values() if c['reading']=='H' and c['kind']=='decisive')
    check(polarity=={'Y':3,'N':3},'imbalanced polarity')
    tests=mutation_controls(texts,row,case,p,jobs,cases)
    return dict(verified_requests=sum(map(len,hashes.values())), full_rows=192, marked_rows=192, filtered_rows=48,
                exact_marker_substitutions=48, exact_removed_rows=144, one_lamp_both_signs_in_every_record=True,
                distinct_strata=len(permutations_by_slot), schedules=permutations_by_slot, high_decisive=dict(sorted(polarity.items())),
                negative_control_rejections=tests, record_oracle=cases, request_sha256=hashes)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    out=ROOT/'audit'/'displays.json'
    result=run(ROOT)
    data=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if parser.parse_args().write:
        out.write_text(data)
    else:
        check(out.read_bytes()==data.encode(),'archived audit differs')
    print(result['verified_requests'],'requests,',len(result['record_oracle']),'triples,',len(result['negative_control_rejections']),'rejected corruptions')
