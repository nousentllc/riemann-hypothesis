"""Audit the two presentations, signed comparisons and decisions without the study scorer."""
import argparse
import csv
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
PILOT = ROOT / 'pilot'
ARMS = ('raw', 'labeled')
QUESTION = re.compile(r'Question: is the signed current of (R\d+) > (-?\d+(?:/\d+)?) A\?')
EVIDENCE = re.compile(r'The initial comparator reading is ([HL])\.')


def check(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes())


def decide(ids, positive):
    yes = set(ids) & positive
    no = set(ids) - positive
    check(bool(yes or no), 'An empty information set has no verdict.')
    if yes and no:
        return 'U'
    return 'Y' if yes else 'N'


def certificate(answer, ids, positive):
    if not answer or answer['verdict'] != decide(ids, positive):
        return False
    claims = answer['certificate']
    if len(set(claims)) != len(claims):
        return False
    if answer['verdict'] == 'U':
        return (len(claims) == 2 and set(claims) <= ids
                and len(set(claims) & positive) == 1)
    return set(claims) == ids


def inspect_pair(rid, row):
    raw = (PILOT / 'prompts' / (rid + '.raw.txt')).read_bytes().decode()
    labeled = (PILOT / 'prompts' / (rid + '.labeled.txt')).read_bytes().decode()
    a, b = raw.splitlines(keepends=True), labeled.splitlines(keepends=True)
    check(len(a) == len(b), f'{rid}: unequal numbers of presentation lines.')
    target = QUESTION.findall(raw)
    evidence = EVIDENCE.findall(raw)
    check(len(target) == len(evidence) == 1, f'{rid}: target or observed lamp ambiguous.')
    cutoff = Fraction(target[0][1])
    check(cutoff == Fraction(str(row['target_threshold'])), f'{rid}: threshold mismatch.')
    header_index, = [i for i, line in enumerate(a) if line.startswith('ID stu target_current initial ')]
    menu = a[header_index].split()[4:]
    check(menu == list(row['menu']), f'{rid}: menu order mismatch.')
    check(len(menu) == 3, f'{rid}: three measurements expected.')
    check(len(row['states']) == 8, f'{rid}: eight candidates expected.')
    lamps, meters, positive = {}, {}, set()
    switches = set()
    for index, original in enumerate(a):
        body = original.rstrip('\r\n')
        eol = original[len(body):]
        suffix = ''
        if index == header_index:
            suffix = ' target_current_above_threshold'
        if header_index < index <= header_index + 8:
            cols = body.split()
            check(len(cols) == 4 + len(menu), f'{rid}: malformed row {body!r}.')
            sid, bits, value, initial = cols[:4]
            check(sid in row['states'] and sid not in lamps, f'{rid}: duplicate/unknown id {sid}.')
            check(re.fullmatch(r'[01]{3}', bits) is not None, f'{rid}: malformed switch setting.')
            check(set(cols[3:]) <= {'H', 'L'}, f'{rid}: malformed meter state.')
            switches.add(bits)
            state = row['states'][sid]
            check(state['bits'] == bits and Fraction(value) == Fraction(str(state['target_current'])),
                  f'{rid}: incorrect public physical values for {sid}.')
            truth = Fraction(value) > cutoff
            check(truth is state['answer'], f'{rid}: incorrect exact threshold comparison for {sid}.')
            if truth:
                positive.add(sid)
            lamps[sid] = initial
            meters[sid] = dict(zip(menu, cols[4:]))
            check(meters[sid] == state['obs'] and initial == state['initial'],
                  f'{rid}: incorrect public comparator values for {sid}.')
            suffix = ' Y' if truth else ' N'
        check(b[index] == body + suffix + eol,
              f'{rid}: addition differs from the unique permitted change on line {index + 1}.')
    check(len(switches) == 8, f'{rid}: incomplete switch state space.')
    live = {i for i, lamp in lamps.items() if lamp == evidence[0]}
    actual = row['actual']
    check(live == set(row['eligible']) and actual in live, f'{rid}: invalid initial compatible set.')
    initial = decide(live, positive)
    by_meter = {
        m: {v: {s for s in live if meters[s][m] == v} for v in {meters[s][m] for s in live}}
        for m in menu
    }
    actual_cells = {m: parts[meters[actual][m]] for m, parts in by_meter.items()}
    certain = [m for m, parts in by_meter.items() if all(decide(group, positive) != 'U' for group in parts.values())]
    possible = [m for m, parts in by_meter.items() if any(decide(group, positive) != 'U' for group in parts.values())]
    actual_settled = [m for m, ids in actual_cells.items() if decide(ids, positive) != 'U']
    if initial != 'U':
        kind, target_verdict = 'settled', initial
    elif actual_settled:
        kind, target_verdict = 'lookup', decide({actual}, positive)
        check(certain == actual_settled and len(certain) == 1, f'{rid}: success via a lucky actual reply.')
        check(sum(len(parts) > 1 for parts in by_meter.values()) >= 2, f'{rid}: a sole varying meter.')
    else:
        kind, target_verdict = 'ambiguous', 'U'
        check(not possible, f'{rid}: ambiguity lost under an alternative possible reply.')
    return dict(family=row['family'], initial=initial, kind=kind, target=target_verdict, live=live,
                positive=positive, menu=menu, actual=actual, actual_cells=actual_cells, certain=certain,
                by_meter=by_meter, meters=meters, lamps=lamps, cutoff=cutoff, table_lines=a[header_index:header_index+9],
                present=[raw,labeled])


def inspect_panel():
    rows = read(ROOT/'circuits'/'records.json')
    check(len(rows) == 12, 'Study requires 12 distinct records.')
    manifest = read(PILOT/'freeze.json')
    check(manifest['seed'] == 2026112429 and manifest['sessions']==24 and manifest['max_requests']==48, 'Unexpected settings.')
    for filename,expected_hash in manifest['sha256'].items():
        check(sha256((ROOT/filename).read_bytes()).hexdigest() == expected_hash, f'Frozen input changed: {filename}.')
    cases = {rid: inspect_pair(rid, row) for rid,row in rows.items()}
    families = defaultdict(list)
    for rid,c in cases.items():
        families[c['family']].append(rid)
    check(len(families) == 6, 'Study requires six families.')
    for fam,(i,j) in families.items():
        left,right = cases[i],cases[j]
        check(left['live'].isdisjoint(right['live']) and len(left['live'] | right['live']) == 8,
              f'{fam}: twins do not use the two complementary initial readings.')
        check(left['table_lines'] == right['table_lines'], f'{fam}: twins have different calibration tables.')
        check({left['kind'],right['kind']} in ({'settled','lookup'},{'ambiguous','lookup'}),
              f'{fam}: strata unbalanced within family.')
    strata = Counter(c['kind'] for c in cases.values())
    signs = Counter(c['target'] for c in cases.values() if c['kind']=='lookup')
    positions = Counter(c['menu'].index(c['certain'][0])+1 for c in cases.values() if c['kind']=='lookup')
    check(strata == {'settled':3,'lookup':6,'ambiguous':3} and signs == {'Y':3,'N':3},
          f'Unbalanced record types/signs {strata}, {signs}.')
    check(positions == {1:2,2:2,3:2}, f'Unbalanced action positions {positions}.')
    jobs = read(PILOT/'order.json')
    expected_jobs = Counter((rid,a) for rid in rows for a in ARMS)
    check(Counter((j['record'],j['arm']) for j in jobs) == expected_jobs, 'Incomplete paired schedule.')
    wave = {j['record']:j['arm'] for j in jobs[:12]}
    check(len(wave)==12 and all(wave[j['record']] != j['arm'] for j in jobs[12:]),
          'A pair shared one wave.')
    check(sum(wave[rid]=='raw' for rid,c in cases.items() if c['kind']=='lookup')==3,
          'Actionable presentation order is unbalanced.')
    for i,j in families.values():
        check(wave[i]!=wave[j], 'The control and actionable twin had the same first arm.')
    shortcut = {}
    for rid,c in cases.items():
        if c['kind'] != 'lookup':
            continue
        balance = {m: min(len(c['by_meter'][m].get(lamp,set())) for lamp in ('H','L')) for m in c['menu']}
        best = [m for m in c['menu'] if balance[m] == max(balance.values())]
        rate = Fraction(len(set(best) & set(c['certain'])),len(best))
        shortcut[rid] = dict(compatible_states=len(c['live']),max_balance_ties=len(best),
                             uniform_ties_decisive_probability=str(rate))
    expected = sum(Fraction(q['uniform_ties_decisive_probability']) for q in shortcut.values())
    result = dict(records=len(rows),families=len(families),presentations_verified=2*len(rows),
                  signed_fraction_comparisons_verified=8*len(rows),unique_family_candidate_rows=8*len(families),
                  stratum_counts=dict(strata),actionable_signs=dict(signs),decisive_menu_positions=dict(positions),
                  sessions_scheduled=len(jobs), balance_heuristic=shortcut,
                  expected_decisive_uniform_balanced_ties=str(expected))
    return rows,cases,jobs,result


def request_digest(messages, row, seed, first):
    fields = {'verdict': {'enum':['Y','N','U'], 'type':'string'},
              'certificate': {'type':'array', 'minItems':1,'maxItems':len(row['states']),
                              'items': {'type':'string','enum':list(row['states'])}}}
    if first:
        fields['lookup'] = {'type':'string','enum':['NONE',*row['menu']]}
    payload = dict(model='gpt-oss:20b', think='low', stream=False, keep_alive='9m', messages=messages,
                   options={'seed':seed,'temperature':0,'num_ctx':8192,'num_predict':2048},
                   format={'type':'object','required':list(fields),'properties':fields,'additionalProperties':False})
    return sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()


def parse_stage(stage, path, row, first):
    check(stage == read(path), f'Combined receipt differs from {path.name}.')
    status = stage['status']
    check(status in ('ok','error','interrupted','invalid'), f'Unrecognized status in {path}.')
    answer = None
    if stage.get('usage',{}).get('done_reason') == 'stop':
        try:
            item = json.loads(stage['content'])
        except (json.JSONDecodeError, KeyError):
            item = None
        fields = {'verdict','certificate','lookup'} if first else {'verdict','certificate'}
        if (isinstance(item,dict) and set(item)==fields and item['verdict'] in ('Y','N','U')
                and isinstance(item['certificate'],list) and all(isinstance(z,str) and z in row['states'] for z in item['certificate'])
                and (not first or item['lookup'] in ['NONE',*row['menu']])):
            answer = item
    check(answer == stage['answer'] and (status=='ok') == (answer is not None),
          f'Decoded answer disagrees with receipt status/content at {path}.')
    return answer


def inspect_results(rows,cases,jobs,pre):
    if not (PILOT/'results'/'summary.json').is_file():
        raise ValueError('Score release unavailable. Do not inspect incomplete runs.')
    official = read(PILOT/'results'/'summary.json')
    with (PILOT/'results'/'cases.csv').open(encoding='utf8',newline='') as fp:
        table = {(r['record'],r['arm']):r for r in csv.DictReader(fp)}
    check(len(table)==24, 'Incomplete case decision table.')
    conclusion = {}
    names = ('productive','actionable_certified','certified','unsupported','requests','parseable_final',
             'scored_sessions','initial_certificate','target_final','licensed_final','terminal_certificate',
             'service_nanoseconds','input_tokens','output_tokens')
    totals = {a:Counter(dict.fromkeys(names,0)) for a in ARMS}
    for job in jobs:
        rid,arm = job['record'],job['arm']
        row,c = rows[rid],cases[rid]
        key = f'{rid}_{arm}'
        directory = PILOT/'observed'/key
        session = read(directory/'session.json')
        check(session['record']==rid and session['arm']==arm,f'{key}: corrupted identity.')
        tally = totals[arm]
        tally['scored_sessions'] += 1
        pool = c['live'].copy()
        observed = 'NONE'
        first = None
        last = None
        unsupported = 0
        system = (PILOT/'method.txt').read_text().strip()
        messages = [dict(role='system',content=system),
                    dict(role='user',content=c['present'][ARMS.index(arm)])]
        seed = 2026112429+int(rid.rsplit('-',1)[1])
        for stage_name in ('first', 'second'):
            initial = (stage_name=='first')
            expected_stage = initial or observed in c['menu']
            check((stage_name in session)==expected_stage and (directory/(stage_name+'.json')).is_file()==expected_stage,
                  f'{key}: missing or extraneous {stage_name} stage.')
            if not expected_stage:
                break
            stage = session[stage_name]
            last = parse_stage(stage,directory/(stage_name+'.json'),row,initial)
            digest = request_digest(messages,row,seed if initial else seed+1000,initial)
            check(digest==stage['request_sha256'],f'{key}: {stage_name} request bytes differed.')
            tally['requests'] += 1
            usage = stage.get('usage',{})
            tally['input_tokens'] += usage.get('prompt_eval_count') or 0
            tally['output_tokens'] += usage.get('eval_count') or 0
            tally['service_nanoseconds'] += usage.get('total_duration') or 0
            if last and last['verdict'] in ('Y','N') and last['verdict'] != decide(pool,c['positive']):
                unsupported += 1
            if initial:
                first = last
                observed = last['lookup'] if last else None
                if observed in c['menu']:
                    reply = c['meters'][c['actual']][observed]
                    check(session['observation'] == {'item':observed,'value':reply},f'{key}: incorrect meter reply.')
                    pool = c['actual_cells'][observed]
                    text = (f'Lookup {observed} returns: {reply}. Give the final verdict and the certificate '
                            'for the evidence now available. Return only verdict and certificate.')
                    messages += [dict(role='assistant',content=stage['content']),dict(role='user',content=text)]
                else:
                    check('observation' not in session,f'{key}: observation delivered without lookup.')
        final_vote = last.get('verdict') if last else None
        productive = c['kind']=='lookup' and observed in c['certain']
        valid_final = certificate(last,pool,c['positive'])
        success = valid_final and final_vote==c['target']
        initial_vote = first.get('verdict') if first else None
        initial_cert = certificate(first,c['live'],c['positive'])
        warranted = decide(pool,c['positive'])
        tally['productive'] += int(productive)
        tally['actionable_certified'] += int(c['kind']=='lookup' and success)
        tally['certified'] += int(success)
        tally['unsupported'] += unsupported
        tally['parseable_final'] += int(final_vote is not None)
        tally['initial_certificate'] += int(initial_cert)
        tally['target_final'] += int(c['target']==final_vote)
        tally['licensed_final'] += int(final_vote==warranted)
        tally['terminal_certificate'] += int(valid_final)
        score = table[rid,arm]
        comparison = dict(target=c['target'],kind=c['kind'],productive=productive,success=success,unsupported=unsupported)
        for k,value in comparison.items():
            check(score[k].lower()==str(value).lower(),f'{key}: independent {k} differs from table.')
        for k,value in {'initial':initial_vote,'final':final_vote,'lookup':observed}.items():
            check(score[k]==('' if value is None else value),f'{key}: independent {k} differs from table.')
        conclusion[key] = dict(record=rid,arm=arm,kind=c['kind'],initial=initial_vote,initial_valid=initial_cert,
                               chosen=observed,decisive=c['certain'] if c['kind']=='lookup' else None,
                               actual_reply=session.get('observation'),final=final_vote,final_warrant=warranted,
                               final_certified=valid_final,possible_ids_after=sorted(pool),target=c['target'],
                               success=success,productive=productive,unsupported=unsupported)
    for arm,tally in totals.items():
        for k in ('productive','actionable_certified','certified','unsupported'):
            check(tally[k]==official['totals'][arm].get(k,0), f'{arm}: independent total {k} differs.')
    paired = Counter()
    for rid,c in cases.items():
        if c['kind']!='lookup':
            continue
        raw = conclusion[rid+'_raw']['productive']
        labeled = conclusion[rid+'_labeled']['productive']
        label = ('both' if raw else 'labeled_only') if labeled else ('raw_only' if raw else 'neither')
        paired[label] += 1
    gate = (totals['labeled']['productive']-totals['raw']['productive']>=2
            and totals['labeled']['actionable_certified']-totals['raw']['actionable_certified']>=1)
    return dict(independently_scored_sessions=len(conclusion),request_hashes_checked=sum(t['requests'] for t in totals.values()),
                totals=totals,actionable_pairs={k:paired[k] for k in ('both','neither','raw_only','labeled_only')},
                representation_follow_up_gate=gate,cases=conclusion,panel=pre)


def report(path, content):
    serialized = json.dumps(content, indent=2, sort_keys=True, ensure_ascii=False)+'\n'
    path.write_text(serialized)
    print(serialized.rstrip())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage', choices=('pre','post'))
    args = p.parse_args()
    rows,cases,jobs,pre = inspect_panel()
    if args.stage == 'pre':
        report(ROOT/'audit'/'pre.json',pre)
    else:
        report(ROOT/'audit'/'post.json', inspect_results(rows,cases,jobs,pre))


if __name__ == '__main__':
    main()
