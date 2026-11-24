"""Reconstruct the forced-reading panel, requests, and terminal answers without importing the study runner."""
import argparse
import csv
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import comb
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ARMS = ('full','filtered')
SEED = 2026112443
MODEL = 'gpt-oss:20b'
DIGEST = '17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes())


def verdict(ids, positive):
    require(bool(ids), 'No surviving switch settings.')
    targets = {i in positive for i in ids}
    return 'U' if len(targets) == 2 else ('Y' if True in targets else 'N')


def judge(answer, live, positive):
    v = answer['verdict'] if answer else None
    ids = answer['certificate'] if answer else []
    picked = set(ids)
    true_sign = verdict(live, positive)
    exact = bool(answer) and len(ids) == len(picked) and picked == live
    # All observed cells have size two. In mixed cells these are the only two possible opposite witnesses.
    require(len(live)==2, 'This equivalence is specific to two-member cells.')
    return dict(verdict=v, target=true_sign, ids=ids, exact_ids=exact, sign=v==true_sign,
                certified=exact and (v==true_sign), unsupported=v in ('Y','N') and v!=true_sign,
                invalid_or_missing=answer is None, excludes=sorted(picked-live), omits=sorted(live-picked),
                duplicate_count=len(ids)-len(picked))


def paired(pairs):
    outcomes=Counter(tuple(map(bool,p)) for p in pairs)
    w,l=outcomes[False,True],outcomes[True,False]
    n=w+l
    allocations=[sum(pattern) for pattern in product((0,1),repeat=n)]
    stat=abs(w-l)
    p_exact=Fraction(sum(abs(2*s-n)>=stat for s in allocations),2**n)
    def tail(x,right):
        return sum(comb(n,k)*x**k*(1-x)**(n-k)
                   for k in range(n+1) if (k>=w if right else k<=w))
    bounds=None
    if n:
        def endpoint(right):
            lo,hi=Fraction(0),Fraction(1)
            for _ in range(50):
                mid=(lo+hi)/2
                if (tail(mid,True)<Fraction(1,40) if right else tail(mid,False)>Fraction(1,40)):
                    lo=mid
                else:
                    hi=mid
            return float((lo+hi)/2)
        bounds=[0 if not w else endpoint(True),1 if not l else endpoint(False)]
    return dict(n=len(pairs),both=outcomes[True,True],neither=outcomes[False,False],
                full_only=l,filtered_only=w,net=w-l,
                exact_two_sided_sign_p=str(p_exact),conditional_win_95pct=bounds)


def request_hash(system, prompt, allowed_ids, seed):
    fields={'verdict':{'type':'string','enum':['Y','N','U']},
            'certificate':{'type':'array','items':{'type':'string','enum':allowed_ids},
                           'minItems':1,'maxItems':8}}
    payload=dict(model=MODEL,messages=[dict(role='system',content=system),dict(role='user',content=prompt)],
                 format={'type':'object','properties':fields,'required':['verdict','certificate'],'additionalProperties':False},
                 stream=False,keep_alive='9m',options=dict(seed=seed,temperature=0,num_ctx=8192,num_predict=2048),
                 think='low')
    return sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()


def decode(receipt, allowed):
    status=receipt['status']
    require(status in ('ok','invalid','interrupted','error'), 'Unexpected response status.')
    decoded=None
    if receipt.get('usage',{}).get('done_reason')=='stop':
        try:
            item=json.loads(receipt.get('content',''))
        except (json.JSONDecodeError, TypeError):
            item=None
        if (isinstance(item,dict) and set(item)=={'verdict','certificate'}
                and item['verdict'] in ('Y','N','U') and isinstance(item['certificate'],list)
                and all(isinstance(i,str) and i in allowed for i in item['certificate'])):
            decoded=item
    require(decoded==receipt['answer'] and (status=='ok')==(decoded is not None),
            'Response as recorded differs from visible text or completion status.')
    return decoded


def baselines(cases):
    metrics={}
    for rid,case in cases.items():
        obs=case['live']; positive=case['positive']
        rows=case['order']
        offer={
            'full_copy_all_unanimity':rows,
            'full_copy_first_two_unanimity':rows[:2],
            'full_initial_lamp_only':[i for i in rows if i in case['by_initial']],
            'full_forced_lamp_only':[i for i in rows if i in case['by_forced']],
            'filtered_copy_all_unanimity':[i for i in rows if i in obs],
        }
        result={}
        for name,ids in offer.items():
            ans={'certificate':ids,'verdict':verdict(ids,positive)}
            s=judge(ans,obs,positive)
            result[name]={'sign':s['sign'],'exact_ids':s['exact_ids'],'certified':s['certified']}
        for name,ids in [('full_copy_all_first_sign',rows),('filtered_copy_all_first_sign',offer['filtered_copy_all_unanimity'])]:
            ans={'certificate':ids,'verdict':verdict([ids[0]],positive)}
            s=judge(ans,obs,positive)
            result[name]={'sign':s['sign'],'exact_ids':s['exact_ids'],'certified':s['certified']}
        metrics[rid]=result
    names=next(iter(metrics.values()))
    counts={name:{k:{f:sum(m[name][f] for rid,m in metrics.items() if cases[rid]['kind']==k)
                     for f in ('sign','exact_ids','certified')}
                  for k in ('decisive','ambiguous')} for name in names}
    return {'definition':'Unanimity gives Y if all listed rows meet the target, N if none, U otherwise. Each policy submits the complete list it selected. First-sign ignores later rows when choosing the verdict.',
            'counts':counts,'per_record':metrics}


def verify_digest_map(root,freeze):
    for n,h in freeze['sha256'].items():
        require(sha256((root/n).read_bytes()).hexdigest()==h,'Frozen bytes changed: '+n)


def materialize_pair(root, rid, r):
    texts={a:(root/'pilot'/'prompts'/f'{rid}.{a}.txt').read_bytes().decode() for a in ARMS}
    full=texts['full']
    questions=re.findall(r'(?m)^Question: is the signed current of (R\d+) > (-?\d+(?:/\d+)?) A\?$',full)
    obs=re.findall(r'(?m)^Observed readings: initial = ([HL]); ([A-Za-z0-9]+) = ([HL])\.$',full)
    require(questions==[(r['signed_branch'], str(r['target_threshold']))],f'{rid}: printed claim or cutoff disagrees.')
    require(obs==[(r['initial_reading'],r['meter'],r['reading'])],f'{rid}: printed forced observations disagree.')
    lines=full.splitlines(keepends=True)
    header_indices=[i for i,line in enumerate(lines) if line.startswith('ID ')]
    require(len(header_indices)==1, f'{rid}: ambiguous or absent calibration header.')
    j=header_indices[0]
    header=lines[j].strip().split()
    require(header[:4]==['ID','stu','target_current','initial'] and header[-1]=='target_current_above_threshold',f'{rid}: unknown column schema.')
    meters=header[4:-1]
    require(len(meters)==len(set(meters)) and set(meters)==set(r['menu']), f'{rid}: changed meter order/membership.')
    states=r['states']
    require(len(states)==8 and len(lines)>j+8, f'{rid}: missing rows/text.')
    positive=set(); sources={}; meters_by_id={}; all_ids=[];switches=set()
    cutoff=Fraction(str(r['target_threshold']))
    for line in lines[j+1:j+9]:
        c=line.split()
        require(len(c)==len(header),f'{rid}: malformed calibration row.')
        sid,bits,amps,first=c[:4]
        require(sid in states and sid not in all_ids and re.fullmatch(r'[01]{3}',bits),f'{rid}: invalid state ID or switches.')
        require(first in ('H','L') and all(v in ('H','L') for v in c[4:-1]),f'{rid}: invalid lamp level.')
        sw=states[sid];target=Fraction(amps)>cutoff
        require(sw['answer'] is target and c[-1]==('Y' if target else 'N'),f'{rid}: strict sign or printed truth bit differs.')
        require(Fraction(str(sw['target_current']))==Fraction(amps) and sw['bits']==bits and sw['initial']==first,
                f'{rid}: exact physical record differs.')
        meter=dict(zip(meters,c[4:-1]))
        require(meter==sw['obs'], f'{rid}: meter values differ.')
        sources[sid]=first; meters_by_id[sid]=meter;all_ids.append(sid);switches.add(bits)
        if target:
            positive.add(sid)
    require(len(switches)==8 and all_ids==r['state_order'], f'{rid}: incomplete switch set or changed printed ordering.')
    by_initial={sid for sid in all_ids if sources[sid]==r['initial_reading']}
    by_forced={sid for sid in all_ids if meters_by_id[sid][r['meter']]==r['reading']}
    live=by_initial&by_forced
    require(by_initial==set(r['eligible']) and live==set(r['survivors']) and len(by_initial)==4 and len(live)==2,
            f'{rid}: observed lamps or survivor list disagreed.')
    require(len(by_initial&positive)==2 and len(by_initial-positive)==2,f'{rid}: initial state set is unbalanced.')
    reconstruction=''.join(lines[:j+1]+[line for sid,line in zip(all_ids,lines[j+1:j+9]) if sid in live]+lines[j+9:])
    require(texts['filtered']==reconstruction,f'{rid}: experimental change exceeds exactly six rows deleted.')
    target=verdict(live,positive)
    kind='ambiguous' if target=='U' else 'decisive'
    require(kind==r['kind'],f'{rid}: stratum disagreed.')
    return dict(rid=rid,params=r,kind=kind,live=live,positive=positive,by_initial=by_initial,
                by_forced=by_forced,order=all_ids,table_lines=lines[j:j+9],target=target,texts=texts)


def inspect_pre(root):
    pilot=root/'pilot'
    freeze=read(pilot/'freeze.json')
    require(freeze['seed']==SEED and freeze['sessions']==36 and freeze['max_requests']==36, 'Unexpected seed, sample size, or request limit.')
    require(freeze['model']=={'tag':MODEL,'digest':DIGEST,'think':'low','max_tokens':2048}
            and freeze['ollama']=='0.40.18' and freeze['direct_api_spend_cap_usd']==0,'Model, serving version or budget differs.')
    verify_digest_map(root,freeze)
    rows=read(root/'circuits'/'records.json')
    require(len(rows)==18,'Expected 18 records.')
    cases={rid:materialize_pair(root,rid,r) for rid,r in rows.items()}
    families=defaultdict(list)
    for case in cases.values():
        families[case['params']['family']].append(case)
    require(len(families)==6,'Expected six layouts.')
    high=Counter()
    for fam,items in families.items():
        decisive=[c for c in items if c['kind']=='decisive']
        controls=[c for c in items if c['kind']=='ambiguous']
        require(len(decisive)==2 and len(controls)==1,f'{fam}: need two decisive and one mixed cell.')
        require(all(c['table_lines']==items[0]['table_lines'] for c in items),f'{fam}: calibration table differs between snapshots.')
        require(all(c['by_initial']==items[0]['by_initial'] for c in items),f'{fam}: distinct initial restriction.')
        twin=decisive[0]; alt=decisive[1]
        require(twin['params']['meter']==alt['params']['meter'] and twin['params']['reading']!=alt['params']['reading'],
                f'{fam}: different decisive instruments or duplicate reading.')
        require(twin['live'].isdisjoint(alt['live']) and twin['live']|alt['live']==twin['by_initial'] and {twin['target'],alt['target']}=={'Y','N'},
                f'{fam}: decisive pair does not partition initial survivors into opposite verdicts.')
        require(controls[0]['params']['meter']!=twin['params']['meter'], f'{fam}: control meter equals decisive meter.')
        for c in items:
            require(len(c['by_forced'])==4 and verdict(c['by_forced'],c['positive'])=='U',
                    f"{c['rid']}: second observation alone supplies a verdict or a different-sized subset.")
            if c['kind']=='decisive' and c['params']['reading']=='H':
                high[c['target']]+=1
    require(high=={'Y':3,'N':3},f'High lamps do not counterbalance target signs: {high}.')
    jobs=read(pilot/'order.json')
    require(Counter((j['record'],j['arm']) for j in jobs)==Counter((r,a) for r in rows for a in ARMS),'Unpaired or missing view.')
    wave={j['record']:j['arm'] for j in jobs[:18]}
    require(len(wave)==18 and all(wave[j['record']]!=j['arm'] for j in jobs[18:]),'Two-wave assignment differs.')
    firsts=Counter((c['kind'],wave[r]) for r,c in cases.items())
    require(firsts=={('decisive','full'):6,('decisive','filtered'):6,('ambiguous','full'):3,('ambiguous','filtered'):3},
            'Within-stratum first-appearance order is unbalanced.')
    for group in families.values():
        a,b=(c for c in group if c['kind']=='decisive')
        require(wave[a['rid']]!=wave[b['rid']],'Within-layout decisive readings have the same first arm.')
    summary=dict(physical_layouts=6,records=len(rows),paired_sessions=len(jobs),target_counts=dict(Counter(c['target'] for c in cases.values())),
                 high_lamp_direction=dict(high),full_rows_verified=8*len(rows),filtered_rows_verified=2*len(rows),
                 one_lamp_available_verdicts={'initial':dict(Counter(verdict(c['by_initial'],c['positive']) for c in cases.values())),
                                              'forced':dict(Counter(verdict(c['by_forced'],c['positive']) for c in cases.values()))},
                 policy_baselines=baselines(cases),record_oracle={rid:dict(family=c['params']['family'],kind=c['kind'],
                     initial_only=sorted(c['by_initial']),forced_only=sorted(c['by_forced']),joint=sorted(c['live']),
                     verdict=c['target'],forced_meter=c['params']['meter'],forced_value=c['params']['reading'])
                     for rid,c in cases.items()})
    return cases,families,jobs,summary


def inspect_post(root,cases,families,jobs):
    pilot=root/'pilot'
    require((pilot/'results'/'summary.json').is_file(),'Wait for the entire run and the released score table before opening outcomes.')
    official=read(pilot/'results'/'summary.json')
    with (pilot/'results'/'cases.csv').open(newline='') as f:
        entries=list(csv.DictReader(f))
    table={(r['record'],r['arm']):r for r in entries}
    require(len(table)==len(entries)==36,'Invalid released case table.')
    numbers={r:i for i,r in enumerate(sorted(cases))}
    system=(pilot/'method.txt').read_text().strip()
    data={}; totals={a:Counter() for a in ARMS}
    for job in jobs:
        rid,arm=job['record'],job['arm']; case=cases[rid]; row=case['params']
        directory=pilot/'observed'/f'{rid}_{arm}'
        require([p.name for p in directory.glob('*.json')]==['response.json'],f'{rid}/{arm}: not one terminal receipt.')
        receipt=read(directory/'response.json')
        allowed=list(row['states'])
        digest=request_hash(system,case['texts'][arm],allowed,SEED+numbers[rid])
        require(digest==receipt['request_sha256'],f'{rid}/{arm}: request text, enumerated IDs, seed, schema, or inference configuration mismatch.')
        ans=decode(receipt,allowed)
        rec=judge(ans,case['live'],case['positive']);data[rid,arm]=rec
        rec.update(family=row['family'],kind=case['kind'],response_status=receipt['status'],
                   required_ids=sorted(case['live']),request_hash=digest)
        tally=totals[arm];k=case['kind']
        for metric in ('certified','sign','exact_ids','unsupported'):
            tally[metric]+=int(rec[metric])
            tally[metric+'_'+k]+=int(rec[metric])
        tally['completed_text']+=int(ans is not None)
        tally['requests']+=1
        for i in rec['excludes']:
            category=('initial_only' if i in case['by_initial'] else
                      'forced_only' if i in case['by_forced'] else 'neither_lamp')
            tally['excluded_ID_occurrences_'+category]+=1
        tally['responses_with_excluded_ID']+=int(bool(rec['excludes']))
        tally['responses_with_omitted_ID']+=int(bool(rec['omits']))
        tally['responses_with_duplicate_ID']+=int(bool(rec['duplicate_count']))
        tally['unnecessary_abstention']+=int(rec['verdict']=='U' and rec['target']!='U')
        tally['invalid_calls']+=int(receipt['status']!='ok')
        tally['length_capped']+=int(receipt.get('usage',{}).get('done_reason')=='length')
        tally['input_tokens']+=receipt.get('usage',{}).get('prompt_eval_count') or 0
        tally['output_tokens']+=receipt.get('usage',{}).get('eval_count') or 0
        tally['service_ns']+=receipt.get('usage',{}).get('total_duration') or 0
        scored=table[rid,arm]
        for col,val in dict(family=row['family'],kind=k,expected=rec['target'],verdict=rec['verdict'] or '',sign=rec['sign'],
                            ids=rec['exact_ids'],certified=rec['certified'],unsupported=rec['unsupported'],
                            status=receipt['status']).items():
            require(scored[col].lower()==str(val).lower(),f'{rid}/{arm}: scorer mismatch for {col}.')
        defects=('missing' if ans is None else 'pass' if rec['certified'] else
                 'IDs' if rec['sign'] else 'verdict' if rec['exact_ids'] else 'verdict and IDs')
        detail={'certificate':' '.join(rec['ids']), 'required_ids':' '.join(rec['required_ids']),
                'extra':' '.join(rec['excludes']),'omitted':' '.join(rec['omits']),
                'duplicate':str(rec['duplicate_count']>0),'barrier':defects}
        for col,val in detail.items():
            require(scored[col]==val, f'{rid}/{arm}: wrong named IDs or defect class ({col}).')
    layout_metrics={}
    for fam,group in sorted(families.items()):
        decisive=[c['rid'] for c in group if c['kind']=='decisive']
        layout_metrics[fam]={a:all(data[r,a]['certified'] for r in decisive) for a in ARMS}
    primary=paired([tuple(g[a] for a in ARMS) for g in layout_metrics.values()])
    for a in ARMS:
        t=totals[a];t['complete_decisive_families']=sum(g[a] for g in layout_metrics.values())
        for ours,theirs in [('requests','sessions'),('completed_text','parseable'),('invalid_calls','invalid'),
                           ('length_capped','length_limited'),('input_tokens','prompt_tokens'),('output_tokens','generated_tokens'),
                           ('service_ns','service_ns'),('unnecessary_abstention','unnecessary_abstention'),
                           ('complete_decisive_families','complete_decisive_families'),('certified','certified'),('sign','sign'),
                           ('exact_ids','ids'),('unsupported','unsupported'),('certified_decisive','certified_decisive'),
                           ('exact_ids_decisive','ids_decisive'),('certified_ambiguous','certified_ambiguous')]:
            require(t[ours]==official['totals'][a][theirs],f'{a}: summary differs for {theirs}.')
    for k in ('full_only','filtered_only','both','neither','net'):
        require(primary[k]==official['primary'][k],f'Official family pair value {k} differs.')
    require(abs(float(Fraction(primary['exact_two_sided_sign_p']))-official['primary']['two_sided_sign_p'])<1e-12,'Paired exact p-value differs.')
    ours,reported=primary['conditional_win_95pct'],official['primary']['conditional_win_95pct']
    require(ours is None and reported is None or ours is not None and reported is not None and len(reported)==2
            and all(abs(a-b)<1e-12 for a,b in zip(ours,reported)),'Paired conditional interval differs.')
    full,flt=totals['full'],totals['filtered']
    gate=primary['net']>=2 and flt['exact_ids_decisive']>=full['exact_ids_decisive']+2 and flt['certified_ambiguous']>=full['certified_ambiguous']
    require(gate is official['development_signal'],'Prospective resource decision differs.')
    return dict(request_hashes_verified=len(data),totals={a:dict(sorted(totals[a].items())) for a in ARMS},gate=gate,
                primary=primary,complete_decisive_families=layout_metrics,
                cases={f'{r}_{a}':v for (r,a),v in data.items()})


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage',choices=['pre','post'])
    args=p.parse_args()
    cases,families,jobs,report=inspect_pre(ROOT)
    if args.stage=='post':
        report=inspect_post(ROOT,cases,families,jobs)
    path=ROOT/'audit'/f'{args.stage}.json'
    path.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'record_oracle','policy_baselines','cases','totals'}}, indent=2))


if __name__=='__main__':
    main()
