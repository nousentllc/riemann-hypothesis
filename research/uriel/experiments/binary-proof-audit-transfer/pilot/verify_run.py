"""Reproduce the frozen presentations, request identities, paired outcome and aggregate counts offline."""
import csv
import hashlib
import json
from collections import Counter, defaultdict
from domain import HERE, MODELS, SEED, ARMS, build_data, public_task
from register_scored import scored_rows
from run import check_manifest, schema

def sha_payload(m, messages, row, seed, choose):
    payload={'model':m['tag'],'messages':messages,'format':schema(row,choose),'stream':False,'keep_alive':'9m',
       'options':{'seed':seed,'temperature':0,'num_ctx':8192,'num_predict':m['max_tokens']}}
    if 'think' in m: payload['think']=m['think']
    return hashlib.sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()

def recover_verdict(row, pool):
    positives=sum(row['states'][s]['answer'] for s in pool)
    if positives==0:return 'N'
    if positives==len(pool):return 'Y'
    return 'U'

def certified(row,pool,answer):
    if not answer or answer['verdict']!=recover_verdict(row,pool):return False
    ids=answer['certificate']
    if answer['verdict']=='U':
        return len(ids)==2 and all(i in pool for i in ids) and row['states'][ids[0]]['answer']!=row['states'][ids[1]]['answer']
    return sorted(ids)==sorted(pool)

def verify(part,model):
    folder,manifest=check_manifest(part,model,False)
    rebuilt=scored_rows() if part=='test' else build_data()['dev']
    rows=json.loads((folder/'records.json').read_text())
    if rebuilt!=rows:raise ValueError('Case regeneration differed')
    score_root=HERE/'reports'/folder.name
    ledger=json.loads((score_root/'summary.json').read_text())
    with (score_root/'cases.csv').open() as f:
        case_table={(r['record'],r['arm']):r for r in csv.DictReader(f)}
    totals={a:Counter() for a in ARMS}; pairs=defaultdict(lambda:defaultdict(list))
    jobs=json.loads((folder/'order.json').read_text())
    assert {(j['record'],j['arm']) for j in jobs}==set(case_table)=={(r,a) for r in rows for a in ARMS}
    checks=Counter()
    for job in jobs:
        rid,arm=job['record'],job['arm']; row=rows[rid]; model_info=MODELS[model]
        out=HERE/'observed'/folder.name/(rid+'_'+arm)
        session=json.loads((out/'session.json').read_text()); seed=SEED+int(rid.split('-')[-1])
        support=set(row['eligible']); full_support=support.copy(); opts=row['menu']
        parts={k:[s for s in full_support if row['states'][s]['obs'][k]==row['states'][row['actual']]['obs'][k]] for k in opts}
        best=recover_verdict(row,support)
        if any(recover_verdict(row,p)!='U' for p in parts.values()):best='Y' if row['states'][row['actual']]['answer'] else 'N'
        messages=[{'role':'system','content':(HERE/'instructions'/(arm+'.txt')).read_text().strip()},
            {'role':'user','content':public_task(row)}]
        last=None
        for stage in ('first','second'):
            if stage not in session:continue
            sr=session[stage]
            assert json.loads((out/(stage+'.json')).read_text())==sr
            assert sr['request_sha256']==sha_payload(model_info,messages,row,seed if stage=='first' else seed+1000,stage=='first')
            checks['request_hashes']+=1;totals[arm]['calls']+=1
            totals[arm]['prompt_tokens']+=sr.get('usage',{}).get('prompt_eval_count') or 0
            totals[arm]['generated_tokens']+=sr.get('usage',{}).get('eval_count') or 0
            last=sr['answer']
            if last:
                assert last==json.loads(sr['content'])
                totals[arm]['unsupported']+=int(last['verdict'] in ('Y','N') and recover_verdict(row,support)!=last['verdict'])
            if stage=='first':
                lookup=last['lookup'] if last else 'NONE'
                if lookup=='NONE':assert 'second' not in session;break
                assert lookup in opts and 'second' in session
                support=set(parts[lookup]);value=row['states'][row['actual']]['obs'][lookup]
                messages+=[{'role':'assistant','content':sr['content']},{'role':'user',
                    'content':f'Lookup {lookup} returns: {value}. Give the final verdict and the certificate for the evidence now available. Return only verdict and certificate.'}]
        good=bool(certified(row,support,last) and last['verdict']==best)
        assert good==(case_table[rid,arm]['success']=='True')
        totals[arm]['certified_cases']+=int(good)
        totals[arm]['certified_determinate']+=int(good and best!='U')
        pairs[row['domain'],row['family']][arm].append(good);checks['sessions']+=1
    for arm,counts in totals.items():
        for k,v in counts.items(): assert ledger['totals'][arm][k]==v,(arm,k,v)
    by_arm={a:sum(all(arms[a]) for arms in pairs.values()) for a in ARMS}
    assert all(sum(r[a] for r in ledger['families'])==by_arm[a] for a in ARMS)
    if part=='test':
        changes=[sum(all(arms['method'])-all(arms['general']) for (d,_),arms in pairs.items() if d==dom)
                  for dom in ('formal','circuits')]
        gate=min(changes)>=1 and totals['method']['unsupported']<=totals['general']['unsupported'] and totals['method']['certified_determinate']>=totals['general']['certified_determinate']
        assert gate==ledger['advance']
    return dict(registry=folder.name,checks=checks,complete_families=by_arm)

if __name__=='__main__':
    import sys
    print(json.dumps(verify(*sys.argv[1:]),indent=2))
