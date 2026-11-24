"""Read the saved requests and visible responses without importing the instrument or scorer."""
from collections import Counter
from datetime import datetime
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import csv
import json
import re

ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'pilot'
ARMS=('direct','label_first')

def read(path): return json.loads(path.read_bytes())
def require(ok,message):
    if not ok: raise ValueError(message)
def sha(obj): return sha256(json.dumps(obj,sort_keys=True).encode()).hexdigest()
def combine(v):
    return {('N','N'):'N',('N','Y'):'U',('Y','N'):'U',('Y','Y'):'Y'}[tuple(v)]

def request(r,mode,messages,seed):
    prop={i:{'type':'string','enum':['Y','N']} for i in r['survivors']} if mode=='labels' else {
        'verdict':{'type':'string','enum':['Y','N','U']},
        'certificate':{'type':'array','items':{'type':'string','enum':list(r['states'])},'minItems':1,'maxItems':8}}
    return dict(model='gpt-oss:20b',messages=messages,format=dict(type='object',properties=prop,required=list(prop),additionalProperties=False),
                stream=False,keep_alive='9m',think='low',options=dict(seed=seed,temperature=0,num_ctx=8192,num_predict=2048))

def no_duplicates(pairs):
    if len(dict(pairs))!=len(pairs):raise ValueError('Duplicate JSON key.')
    return dict(pairs)

def observed(directory, payload, row, mode):
    saved=read(directory/'request.json')
    require(saved==payload,'Unexpected payload '+str(directory))
    r=read(directory/'response.json')
    require(r['request_sha256']==sha(saved),'Unbound response '+str(directory))
    ans=None
    if r.get('usage',{}).get('done_reason')=='stop':
        try: raw=json.loads(r.get('content',''),object_pairs_hook=no_duplicates)
        except (ValueError,TypeError):raw=None
        if isinstance(raw,dict):
            if mode=='labels':
                if set(raw)==set(row['survivors']) and all(v in ('Y','N') for v in raw.values()):ans=raw
            elif (set(raw)=={'verdict','certificate'} and raw['verdict'] in ('Y','N','U') and isinstance(raw['certificate'],list)
                  and 1<=len(raw['certificate'])<=8 and all(s in row['states'] for s in raw['certificate'])):ans=raw
    require(ans==r['answer'] and (ans is not None)==(r['status']=='ok'),'Visible response mismatch '+str(directory))
    return r

def audit():
    reg=read(P/'freeze.json')
    for name,h in reg['sha256'].items():require(sha256((ROOT/name).read_bytes()).hexdigest()==h,name)
    schedule=read(P/'order.json')
    rows=read(ROOT/'circuits/records.json')
    with (P/'results/cases.csv').open(newline='') as f:official={(r['record'],r['arm']):r for r in csv.DictReader(f)}
    require(len(official)==len(schedule)==48,'Incomplete official ledger')
    counts={a:Counter() for a in ARMS}; typ={}; data={}; families={}; stages=[]; flow=Counter()
    last=None
    for job in schedule:
        rid,arm=job['record'],job['arm'];row=rows[rid];folder=P/'observed'/f'{rid}_{arm}'
        mode='labels' if arm=='label_first' else 'direct'
        prompts={m:(P/'prompts'/f'{rid}.{m}.txt').read_text() for m in ('direct','labels')}
        direct,labels=(s.splitlines() for s in prompts.values())
        require(direct[:-1]==labels[:-1], 'Shared evidence diff')
        visible=[x.split() for x in direct if x.startswith('. ')]
        first,second=list(row['menu'])
        matching={sid for sid,s in row['states'].items() if s['initial']==row['initial_reading'] and s['obs'][row['meter']]==row['reading']}
        refs={}
        for mark,sid,bits,current,initial,m1,m2,target in visible:
            state=row['states'][sid]
            require((bits,initial,m1,m2)==(state['bits'],state['initial'],state['obs'][first],state['obs'][second]),'Wrong table')
            polarity='Y' if Fraction(current)>Fraction(row['target_threshold']) else 'N'
            require(Fraction(current)==Fraction(state['target_current']) and polarity==target,'Wrong sign')
            refs[sid]=target
        require(len(visible)==2 and set(refs)==matching and list(refs)==row['survivors'],'Wrong public survivors')
        target=combine(refs.values()); pattern=''.join(refs.values())
        msgs=[dict(role='system',content=(P/'method.txt').read_text().strip()),dict(role='user',content=prompts[mode])]
        seed=2026112467+sorted(rows).index(rid)
        payload=request(row,mode,msgs,seed+(1000 if mode=='labels' else 0))
        require(sha(payload)==job['first_request_hash'],'Frozen job mismatch')
        initial=observed(folder/mode,payload,row,mode)
        trace=[(mode,initial)]; terminal=initial; reported=None
        if mode=='labels':
            reported=initial['answer']
            msg2=[*msgs,dict(role='assistant',content='{VERBATIM_VISIBLE_LABEL_RESPONSE}'),dict(role='user',content=direct[-1])]
            require(sha(request(row,'verdict',msg2,seed))==job['verdict_template_hash'],'Template mismatch')
            if reported is not None:
                msg2[-2]['content']=initial['content']
                terminal=observed(folder/'verdict',request(row,'verdict',msg2,seed),row,'verdict')
                trace.append(('verdict',terminal))
            else:
                require(not (folder/'verdict').exists(),'Gated verdict was obtained')
                terminal={'answer':None,'status':'gated'}
        for stage,receipt in trace:
            start,stop=[datetime.fromisoformat(receipt[k]) for k in ('started','ended')]
            require(start<=stop and (last is None or last<=start),'Overlapping or out-of-order calls')
            require(start>datetime.fromisoformat('2026-11-24T14:42:31-05:00'),'Call predates public registration')
            last=stop
            stages.append(dict(record=rid,arm=arm,stage=stage,status=receipt['status'],start=start.isoformat(),end=stop.isoformat(),seconds=(stop-start).total_seconds()))
        ans=terminal['answer'] or {};v=ans.get('verdict');ids=ans.get('certificate',[])
        hits=None if reported is None else sum(reported[s]==refs[s] for s in refs)
        implied=None if reported is None else combine([reported[s] for s in refs])
        val=dict(pattern=pattern,truth=target,verdict=v,certificate=' '.join(ids),warranted=v==target,
                 ids_exact=len(ids)==2 and set(ids)==set(refs),label_hits=hits,reported_verdict=implied)
        val['certified']=val['warranted'] and val['ids_exact']
        rec=official[rid,arm]
        for key,x in val.items():require(rec[key]==('' if x is None else str(x)),f'{rid}/{arm} scoring {key}')
        c=counts[arm];c['warranted']+=int(v==target);c['wrong']+=int(v is not None and v!=target);c['missing']+=int(v is None)
        c['certified']+=val['certified']
        families.setdefault(row['family'],{a:0 for a in ARMS})[arm]+=val['warranted']
        if arm=='label_first':
            labeltype=('missing' if hits is None else 'accurate' if hits==2 else 'inaccurate')
            finaltype=('missing' if v is None else 'warranted' if v==target else 'wrong')
            flow[labeltype+' labels / '+finaltype+' verdict']+=1
        typ[rid]=pattern
        data[rid+'_'+arm]=dict(**val,public_labels=refs,committed_labels=reported,final_status=terminal['status'])
    require(len(stages)==len(list((P/'observed').rglob('response.json')))==len(list((P/'observed').rglob('request.json'))),'Unaccounted call')
    require(Counter(typ.values())==dict.fromkeys(('YY','NN','YN','NY'),6),'Pattern imbalance')
    for wave in (schedule[:24],schedule[24:]):
        require(len({j['record'] for j in wave})==24,'Records unpaired across waves')
        require(Counter((typ[j['record']],j['arm']) for j in wave)=={(k,a):3 for k in set(typ.values()) for a in ARMS},'Order imbalance')
    diff=[r['label_first']-r['direct'] for r in families.values()]
    null=Counter(sum(s*d for s,d in zip(sign,diff)) for sign in product((1,-1),repeat=6))
    p=Fraction(sum(n for k,n in null.items() if abs(k)>=abs(sum(diff))),64)
    official_summary=read(P/'results/summary.json')
    require(p==Fraction(official_summary['layout_sign_flip_two_sided']) and families==official_summary['by_family'],'Layout contrast')
    for a,c in counts.items():
        for k,v in c.items():require(v==official_summary['totals'][a][k],a+'/'+k)
    return dict(verified_requests=len(stages),verified_workflows=len(data),stage_order=stages,counts=counts,
                label_flow=flow,families=families,fair_sign_distribution=dict(sorted(null.items())),p_exact=str(p),cases=data)

if __name__=='__main__':
    report=audit()
    (ROOT/'audit/post.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('Verified',report['verified_requests'],'requests and',report['verified_workflows'],'decisions:',dict(report['label_flow']))
