"""Independently reconstruct the forked quantifier requests and rescore visible JSON answers."""
import argparse
from collections import Counter
import csv
from datetime import datetime
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026112479
SYSTEM = 'Read the supplied record. Answer only the question in the current turn using the required JSON format.'
SLOT = '{VERBATIM_VISIBLE_LABEL_RESPONSE}'
QUESTIONS = {
    'any': 'Is the target label Y for at least one of the two survivors?',
    'both': 'Is the target label Y for both of the two survivors?',
}
FORMAT = ' Return only the JSON field answer, using Y for yes and N for no.'
SIGS = ('YY','YN','NY','NN')


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_fields)


def unique_fields(items):
    result = dict(items)
    require(len(result) == len(items), 'Duplicate JSON key')
    return result


def sha(obj):
    return sha256(json.dumps(obj,sort_keys=True).encode()).hexdigest()


def bit(test):
    return 'Y' if test else 'N'


def scope_truth(pattern):
    return bit('Y' in pattern) + bit('N' not in pattern)


def oracle(row):
    states = row['states']
    threshold = Fraction(row['target_threshold'])
    truth = {s: bit(Fraction(x['target_current']) > threshold) for s,x in states.items()}
    require(len(states)==8 and len(set(row['state_order']))==8 and set(row['state_order'])==set(states), 'Eight distinct physical rows')
    require(all((truth[s]=='Y')==x['answer'] for s,x in states.items()), 'Arithmetic truth disagrees')
    first={s for s,x in states.items() if x['initial']==row['initial_reading']}
    second={s for s,x in states.items() if x['obs'][row['meter']]==row['reading']}
    require(all(len(cell)==4 and {truth[s] for s in cell}=={'Y','N'} for cell in (first,second)), 'A single reading shortcuts')
    selected=[s for s in row['state_order'] if s in first and s in second]
    require(len(selected)==2 and selected==row['survivors'], 'Incorrect survivor identities or order')
    return {s:truth[s] for s in selected}


def printed(row, labels):
    ids=list(labels);meters=list(row['menu'])
    lines=[row['description'],
           f"The target label is Y if the signed current of {row['signed_branch']} > {row['target_threshold']} A, and N otherwise.",
           'Initial comparator: '+row['initial_description'],
           'Other comparators: '+' | '.join(m+': '+row['menu'][m] for m in meters),
           'H means a comparator condition holds and L means it fails. All currents are exact amperes.',
           ' '.join(['ID','stu','target_current','initial',*meters,'target_label'])]
    for sid in ids:
        st=row['states'][sid]
        lines.append(' '.join([sid,st['bits'],st['target_current'],st['initial'],*[st['obs'][m] for m in meters],labels[sid]]))
    lines.extend(['', f"Observed readings: initial = {row['initial_reading']}; {row['meter']} = {row['reading']}.",
                  'The table shows exactly the two survivors compatible with the observed readings.',
                  f'Report the target label for each survivor. Return only a JSON object with keys {ids[0]} and {ids[1]}, each having value Y or N.'])
    return '\n'.join(lines)


def payload(msgs, seed, keys):
    props={k:{'type':'string','enum':['Y','N']} for k in keys}
    return dict(model='gpt-oss:20b',messages=msgs,format=dict(type='object',properties=props,
                required=list(keys),additionalProperties=False),stream=False,
                keep_alive='9m',think='low', options=dict(seed=seed,temperature=0,num_ctx=8192,num_predict=2048))


def child(msgs, content, q, seed):
    return payload([*msgs,dict(role='assistant',content=content),dict(role='user',content=QUESTIONS[q]+FORMAT)],seed,['answer'])


def order_for(rows, patterns):
    rng=Random(SEED)
    layouts=sorted({r['family'] for r in rows.values()})
    rng.shuffle(layouts)
    schedule=[]
    for idx,rid in enumerate(sorted(rows)):
        parity=(layouts.index(rows[rid]['family'])+('YY','NN','YN','NY').index(patterns[rid]))%2
        schedule.append((rid,SEED+idx,('both','any') if parity else ('any','both')))
    rng.shuffle(schedule)
    return schedule


def pre(root):
    p=root/'pilot'
    reg=read(p/'freeze.json')
    for name, h in reg['sha256'].items():
        require(sha256((root/name).read_bytes()).hexdigest()==h, 'Frozen hash differs: '+name)
    require(reg['model']==dict(tag='gpt-oss:20b',digest='17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7',max_tokens=2048,think='low')
        and reg['ollama']=='0.40.18' and reg['seed']==SEED and reg['maximum_inferences']==72
        and reg['paid_api_cap_usd']==0 and reg['socket_timeout_seconds']==900,'Model/environment mismatch')
    rows=read(root/'circuits/records.json')
    historical=read(root/'circuits/historical_ids.json')
    older={sid for ids in historical.values() for sid in ids}; newer={sid for r in rows.values() for sid in r['states']}
    require(len(historical)==32 and len(older)==256 and len(newer)==48 and not older.intersection(newer),'Fresh ID check')
    reg_jobs=read(p/'order.json')
    require((p/'method.txt').read_text().strip()==SYSTEM,'Unexpected system instruction')
    labels={i:oracle(row) for i,row in rows.items()}
    patterns={i:''.join(lab.values()) for i,lab in labels.items()}
    expected_order=order_for(rows,patterns)
    require(len(reg_jobs)==len(rows)==24 and len({r['family'] for r in rows.values()})==6,'Wrong panel size')
    exact={}; fam_order=Counter(); pattern_order=Counter()
    for job, expected in zip(reg_jobs,expected_order):
        rid=job['record']; seed=job['seed']; order=tuple(job['query_order']); r=rows[rid]
        require((rid,seed,order)==expected,'Unexpected schedule')
        text=(p/'prompts'/f'{rid}.labels.txt').read_text()
        require(text==printed(r,labels[rid]),'Printed record changed')
        msgs=[dict(role='system',content=SYSTEM),dict(role='user',content=text)]
        checkpoint=payload(msgs,seed+1000,labels[rid])
        require(sha(checkpoint)==job['labels_request_sha256'],'Checkpoint hash differs')
        queries={q:child(msgs,SLOT,q,seed) for q in QUESTIONS}
        require({q:sha(v) for q,v in queries.items()}==job['query_template_sha256'],'Template hash differs')
        require(queries['any']['messages'][:-1]==queries['both']['messages'][:-1],'Checkpoint histories differ')
        fam_order[r['family'],order[0]]+=1; pattern_order[patterns[rid],order[0]]+=1
        exact[rid]=dict(truth=labels[rid],pattern=patterns[rid],expected=scope_truth(patterns[rid]),seed=seed,order=list(order),
                        family=r['family'],labels_request_hash=sha(checkpoint),template_hashes={q:sha(v) for q,v in queries.items()})
    for fam in {r['family'] for r in rows.values()}:
        require(Counter(patterns[i] for i,r in rows.items() if r['family']==fam)==dict.fromkeys(SIGS,1),'Unbalanced family')
        for q in QUESTIONS:require(fam_order[fam,q]==2,'Layout order imbalance')
    require(all(pattern_order[p,q]==3 for p in SIGS for q in QUESTIONS),'Pattern order imbalance')
    return exact


def decoded(content, keys):
    try: answer=json.loads(content,object_pairs_hook=unique_fields)
    except (ValueError,TypeError):return None
    if not isinstance(answer,dict) or set(answer)!=set(keys):
        return None
    return answer if all(v in ('Y','N') for v in answer.values()) else None


def receipt(folder, expected, keys):
    actual=read(folder/'request.json')
    require(actual==expected, 'Unexpected request history, grammar or seed: '+str(folder))
    rec=read(folder/'response.json')
    journal=read(folder/'response.started')
    require(journal=={k:rec[k] for k in ('started','request_sha256')},'Start marker disagrees: '+str(folder))
    require(sha(actual)==rec['request_sha256'],'Unbound response: '+str(folder))
    require(rec['status'] in ('ok','invalid','error','interrupted'),'Unknown status')
    parsed=decoded(rec.get('content'),keys) if rec.get('usage',{}).get('done_reason')=='stop' else None
    require(parsed==rec.get('answer') and (rec['status']=='ok')==(parsed is not None),'Decoded visible text differs')
    return rec


def bounds(ans, sig):
    """Per-case sharp lower and upper indicator for a counterfactual two-bit completion."""
    compatible=all(value is None or value==target for value,target in zip(ans,sig))
    return int(compatible and None not in ans),int(compatible)


def fit(pattern, name):
    q=scope_truth(pattern)
    vals={'scope':q, 'or_on_both':q[0]*2, 'and_on_both':q[1]*2,'reversed':q[::-1],
          'always_yes':'YY','always_no':'NN','wording_only':'YN','first_row_twice':pattern[0]*2,'second_row_twice':pattern[1]*2}
    return vals[name]


def checks(rows):
    names=('scope','or_on_both','and_on_both','reversed','always_yes','always_no','wording_only','first_row_twice','second_row_twice')
    cohorts={'all':list(rows.values()),'mixed':[r for r in rows.values() if r['pattern'][0]!=r['pattern'][1]],
             'accurate_complete':[r for r in rows.values() if r['exact_checkpoint'] and r['complete']],
             'mixed_accurate_complete':[r for r in rows.values() if r['exact_checkpoint'] and r['complete'] and len(set(r['pattern']))==2]}
    matrix={}
    for name in names:
        matrix[name]={}
        for group,cases in cohorts.items():
            ranges=[bounds((r['any'],r['both']),fit(r['pattern'],name)) for r in cases]
            low=sum(a for a,b in ranges);high=sum(b for a,b in ranges)
            matrix[name][group]=dict(n=len(cases),matched=low,possible=high,mismatch=len(cases)-high,undetermined=high-low)
    return matrix


def identify_conflicts(cases):
    """Count branches where an erroneous transcription could distinguish two references."""
    branches={q:dict(different_references=0,followed_physical=0,followed_report=0,missing=0) for q in QUESTIONS}
    map_types=Counter()
    example={}
    for rid,c in cases.items():
        p=c['reported_pattern']
        if p is None:
            kind='missing'
        elif c['exact_checkpoint']:
            kind='exact'
        elif scope_truth(p)==c['expected']:
            kind='inaccurate_but_permutation_equivalent'
        else:
            kind='inaccurate_and_distinguishable'
        map_types[kind]+=1
        if not p or kind=='exact':
            continue
        targets=scope_truth(p)
        split={}
        for i,q in enumerate(QUESTIONS):
            if c['expected'][i]==targets[i]:
                continue
            result='missing' if c[q] is None else 'followed_physical' if c[q]==c['expected'][i] else 'followed_report'
            branches[q]['different_references']+=1
            branches[q][result]+=1
            split[q]=dict(physical=c['expected'][i],reported=targets[i],delivered=c[q],outcome=result)
        example[rid]=dict(transcription_type=kind,discriminating_branches=split)
    return dict(types=dict(map_types),by_question=branches,records=example)


def post(root, predata, registration):
    pp=root/'pilot'; observed=pp/'observed'; scheduled=read(pp/'order.json')
    cases={}; ledger=[];last=None
    registered=datetime.fromisoformat(registration['committed_at'])
    for j in scheduled:
        rid=j['record']; d=predata[rid]; labels=d['truth']; seed=d['seed']
        msgs=[dict(role='system',content=SYSTEM),dict(role='user',content=(pp/'prompts'/f'{rid}.labels.txt').read_text())]
        cp=receipt(observed/rid/'labels',payload(msgs,seed+1000,labels),labels)
        reported=cp['answer']
        available={'any':None,'both':None}; status={q:'gated' for q in QUESTIONS}
        events=[('labels',cp)]
        if reported is None:
            require(all(not (observed/rid/q).exists() for q in QUESTIONS),'Invalid checkpoint leaked to children')
        else:
            for q in d['order']:
                rr=receipt(observed/rid/q,child(msgs,cp['content'],q,seed),['answer'])
                available[q]=rr['answer']['answer'] if rr['answer'] else None
                status[q]=rr['status']
                events.append((q,rr))
        for stage,rr in events:
            begin,end=(datetime.fromisoformat(rr[k]) for k in ('started','ended'))
            require(registered<=begin<=end and (last is None or last<=begin),'Temporal order differs')
            last=end
            ledger.append(dict(record=rid,stage=stage,request_sha256=rr['request_sha256'],started=begin.isoformat(),ended=end.isoformat(),
                               seconds=(end-begin).total_seconds(),status=rr['status'],finish=rr.get('usage',{}).get('done_reason'),
                               usage={k:rr.get('usage',{}).get(k) for k in ('prompt_eval_count','eval_count','total_duration','load_duration','eval_duration')}))
        oriented=[available[q] for q in QUESTIONS]
        complete=None not in oriented
        pattern=d['pattern']
        submitted=''.join(reported[i] for i in labels) if reported else None
        sign=''.join(oriented) if complete else None
        entry=dict(family=d['family'],pattern=pattern,ordered_ids=list(labels),true_labels=labels,
                   expected=d['expected'],checkpoint_status=cp['status'],reported_labels=reported,
                   reported_pattern=submitted,exact_checkpoint=reported==labels,labels_hits=sum(reported[i]==labels[i] for i in labels) if reported else None,
                   order=d['order'],status=status,any=oriented[0],both=oriented[1],complete=complete,signature=sign,
                   joint_warranted=sign==d['expected'],joint_follows_report=sign==scope_truth(submitted) if complete and reported else None,
                   possible_signatures=[s for s in SIGS if bounds(oriented,s)[1]])
        cases[rid]=entry
    require(len(ledger)==len(list(observed.rglob('request.json')))==len(list(observed.rglob('response.json')))==len(list(observed.rglob('response.started'))),'Extraneous or absent call')
    summaries={}
    for name,cohort in {
        'mixed_all':[r for r in cases.values() if r['pattern'][0]!=r['pattern'][1]],
        'mixed_accurate_complete':[r for r in cases.values() if r['pattern'][0]!=r['pattern'][1] and r['exact_checkpoint'] and r['complete']],
        **{p:[r for r in cases.values() if r['pattern']==p] for p in SIGS}
    }.items():
        joint=Counter(r['signature'] if r['complete'] else 'incomplete' for r in cohort)
        summaries[name]=dict(n=len(cohort),signature_counts={s:joint[s] for s in (*SIGS,'incomplete')},
            signature_bounds={s:[joint[s],sum(s in r['possible_signatures'] for r in cohort)] for s in SIGS})
    return dict(registration=registration,verified_requests=len(ledger),cases=cases,stage_order=ledger,
                cohorts=summaries,policy_fit=checks(cases),reference_disagreement=identify_conflicts(cases))


def selftest():
    for pair in product(('Y','N',None),repeat=2):
        completions=[''.join(t) for t in product('YN',repeat=2) if all(o is None or o==v for o,v in zip(pair,t))]
        for s in SIGS:
            require(bounds(pair,s)==(min(int(v==s) for v in completions),max(int(v==s) for v in completions)),'Bounds control')
    require([scope_truth(p) for p in ('NN','NY','YN','YY')]==['NN','YN','YN','YY'],'Truth control')
    require(decoded('{"answer":"Y","answer":"N"}',['answer']) is None,'Duplicate field accepted')
    require(decoded('{"answer":"U"}',['answer']) is None,'Invalid binary alphabet')
    require(decoded('{"A":"N","wrong_id":"Y"}',['A','B']) is None,'Misbound label array')
    return 36


def write_or_verify(path, value, write):
    serialized=json.dumps(value,indent=2)+'\n'
    if write:path.write_text(serialized)
    else:require(path.read_text()==serialized,'Frozen audit output differs: '+str(path))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['pre','post','test'])
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    selftest()
    if args.action=='test':
        print('Verified 36 exhaustively bounded partial-signature cells and label/scope decoding controls.')
        return
    info=pre(ROOT)
    if args.action=='pre':
        write_or_verify(ROOT/'audit/pre.json',info,args.write)
        print('Verified 24 original label requests and 48 frozen counterfactual sibling hashes.')
    else:
        require((ROOT/'pilot/results/summary.json').is_file(),'Official scoring has not finished.')
        info=post(ROOT,info,read(ROOT/'audit/registration.json'))
        compare_official(ROOT,info)
        write_or_verify(ROOT/'audit/post.json',info,args.write)
        print('Verified',info['verified_requests'],'issued requests and',len(info['cases']),'pairs',info['cohorts']['mixed_all'])


def official_projection(rid, case):
    expected=case['expected']
    report=case['reported_pattern']
    record=dict(record=rid, family=case['family'], pattern=case['pattern'], first=case['order'][0],
                first_id=case['ordered_ids'][0], second_id=case['ordered_ids'][1],
                reported_labels=report or '', label_hits=case['labels_hits'] or 0,
                exact_labels=int(case['exact_checkpoint']), labels_status=case['checkpoint_status'])
    for index,q in enumerate(QUESTIONS):
        answer=case[q]
        prop=scope_truth(report)[index] if report else ''
        record.update({q+'_truth':expected[index],q+'_answer':answer or '',q+'_status':case['status'][q],
                       q+'_correct':int(answer==expected[index]),q+'_reported_truth':prop,
                       q+'_coherent':int(answer==prop) if answer and prop else ''})
    record.update(response_pair=''.join(case[q] or '-' for q in QUESTIONS),complete=int(case['complete']),joint_correct=int(case['joint_warranted']))
    return record


def official_aggregate(cases):
    joint=Counter(''.join(c[q] or '-' for q in QUESTIONS) for c in cases)
    tallies={}
    for i,q in enumerate(QUESTIONS):
        tallies[q]=dict(delivered=sum(c[q] is not None for c in cases),
                        physically_correct=sum(c[q]==c['expected'][i] for c in cases),
                        consistent_with_report=sum(c[q]==scope_truth(c['reported_pattern'])[i] for c in cases if c[q] and c['reported_pattern']))
    return dict(n=len(cases),complete=sum(c['complete'] for c in cases),
                signatures={s:joint[s] for s in SIGS},partials={s:n for s,n in joint.items() if '-' in s},
                joint_correct=sum(c['joint_warranted'] for c in cases), branches=tallies)


def compare_official(root,info):
    cases=info['cases']
    results=root/'pilot/results'
    with (results/'cases.csv').open(newline='') as f:
        official=list(csv.DictReader(f))
    independent=[{k:str(v) for k,v in official_projection(rid,c).items()} for rid,c in cases.items()]
    require(len(official)==len(independent),'Scored case count differs')
    for observed,other in zip(official,independent):
        require(observed==other,'Case ledger differs: '+other['record'])
    vec=list(cases.values())
    mixed=[c for c in vec if len(set(c['pattern']))==2]
    summary=read(results/'summary.json')
    expected=dict(
        all=official_aggregate(vec),mixed=official_aggregate(mixed),
        mixed_exact_complete=official_aggregate([c for c in mixed if c['exact_checkpoint'] and c['complete']]),
        mixed_inaccurate_checkpoint=official_aggregate([c for c in mixed if c['reported_pattern'] and not c['exact_checkpoint']]),
        mixed_missing_checkpoint=official_aggregate([c for c in mixed if not c['reported_pattern']]),
        mixed_signature_attainable_bounds=info['cohorts']['mixed_all']['signature_bounds'],
        controls=official_aggregate([c for c in vec if len(set(c['pattern']))==1]),
        by_pattern={p:official_aggregate([c for c in vec if c['pattern']==p]) for p in SIGS},
        by_order={q:official_aggregate([c for c in vec if c['order'][0]==q]) for q in QUESTIONS},
        mixed_by_order={q:official_aggregate([c for c in mixed if c['order'][0]==q]) for q in QUESTIONS},
        by_family={f:official_aggregate([c for c in vec if c['family']==f]) for f in {c['family'] for c in vec}},
        transcription=dict(maps_returned=sum(c['reported_pattern'] is not None for c in vec),
                           exact=sum(c['exact_checkpoint'] for c in vec), matching_fields=sum(c['labels_hits'] or 0 for c in vec),
                           accepted_maps_by_field_hits=dict(Counter(str(c['labels_hits']) for c in vec if c['reported_pattern'])),
                           mixed_id_swaps=sum(c['reported_pattern']==c['pattern'][::-1] for c in mixed)),
        omissions=[dict(record=rid,labels=c['checkpoint_status'],**c['status']) for rid,c in cases.items() if not c['complete']],
        stages={},behavioral_maps={},paid_api_usd=0)
    for stage in ('labels',*QUESTIONS):
        events=[e for e in info['stage_order'] if stage==e['stage']]
        keys=('prompt_eval_count','eval_count','total_duration','load_duration','eval_duration')
        expected['stages'][stage]=dict(issued=len(events),statuses=dict(Counter(e['status'] for e in events)),
            finish=dict(Counter(e['finish'] or 'unavailable' for e in events)),totals={k:sum(e['usage'][k] or 0 for e in events) for k in keys})
    aliases=dict(existence_twice='or_on_both',universal_twice='and_on_both',reversed_scope='reversed')
    for official_name in ('scope','existence_twice','universal_twice','reversed_scope','always_yes','always_no','first_row_twice','second_row_twice'):
        name=aliases.get(official_name,official_name)
        matched={i for i,c in cases.items() if c['signature']==fit(c['pattern'],name)}
        expected['behavioral_maps'][official_name]=dict(full_matches=len(matched),
            mixed_matches=sum(i in matched and len(set(c['pattern']))==2 for i,c in cases.items()),
            full_layouts=sorted(f for f in expected['by_family'] if all(i in matched for i,c in cases.items() if c['family']==f)),
            complete_mismatches=[i for i,c in cases.items() if c['complete'] and i not in matched])
    require(expected.keys()==summary.keys(),'Official summary sections differ')
    for k in expected:
        require(summary[k]==expected[k],'Official summary differs in '+k)


if __name__=='__main__':
    main()
