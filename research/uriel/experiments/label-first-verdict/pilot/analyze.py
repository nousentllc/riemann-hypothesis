"""Score the labels and the terminal verdict as distinct observed decisions."""
import csv
import json
from collections import Counter
from fractions import Fraction
from itertools import product
from instrument import HERE, save
from run import ARMS, ROWS, read, verify

def verdict(labels):
    unique=set(labels)
    if unique=={'Y','N'}: return 'U'
    if unique in ({'Y'},{'N'}): return next(iter(unique))
    raise ValueError('Expected at least one binary truth label')

def reference(differences):
    observed=abs(sum(differences))
    values=[abs(sum(a*b for a,b in zip(s,differences))) for s in product((-1,1),repeat=len(differences))]
    return str(Fraction(sum(v>=observed for v in values),len(values)))

def main():
    verify()
    rows=read(ROWS); cases=[]
    totals={a:Counter() for a in ARMS}; families={}; patterns={}; usage={}; stages={}
    for rid,row in sorted(rows.items()):
        expected={s:('Y' if Fraction(row['states'][s]['target_current'])>Fraction(row['target_threshold']) else 'N') for s in row['survivors']}
        pattern=''.join(expected.values()); target=verdict(expected.values()); family=row['family']
        for arm in ARMS:
            path=HERE/'observed'/f'{rid}_{arm}'
            labels=None; pre=None
            if arm=='label_first':
                pre=read(path/'labels/response.json')
                labels=pre['answer']
            terminal=(read(path/('direct' if arm=='direct' else 'verdict')/'response.json')
                      if arm=='direct' or labels is not None else {'answer':None,'status':'gated'})
            result=terminal['answer'] or {}
            final=result.get('verdict'); ids=result.get('certificate',[])
            hits=sum(labels[s]==expected[s] for s in expected) if labels else None
            implied=verdict(labels.values()) if labels else None
            ids_exact=len(ids)==len(set(ids))==2 and set(ids)==set(expected)
            r=dict(record=rid,family=family,arm=arm,kind=row['kind'],pattern=pattern,truth=target,
                   true_labels=' '.join(k+'='+v for k,v in expected.items()),
                   reported_labels=' '.join(k+'='+v for k,v in (labels or {}).items()),reported_verdict=implied,
                   verdict=final,certificate=' '.join(ids),label_hits=hits,exact_pair=hits==2 if labels else None,
                   coherent=final==implied if final and implied else None,status=terminal['status'],delivered=final is not None,
                   warranted=final==target,wrong=bool(final) and final!=target,ids_exact=ids_exact,certified=(final==target and ids_exact))
            cases.append(r);c=totals[arm]
            c.update({'n':1,'delivered':int(r['delivered']),'missing':int(not r['delivered']),'wrong':int(r['wrong']),
                      'warranted':int(r['warranted']),'certified':int(r['certified']),'ids_exact':int(ids_exact)})
            if arm=='label_first':
                for k,v in {'reported':bool(labels),'labels_correct':hits or 0,'both_labels_correct':hits==2,
                            'accurate_labels_wrong_verdict':hits==2 and r['wrong'],
                            'inaccurate_labels_warranted_verdict':bool(labels) and hits!=2 and r['warranted'],
                            'coherent':r['coherent'] is True,'incoherent':r['coherent'] is False}.items():c[k]+=int(v)
            families.setdefault(family,{a:0 for a in ARMS})[arm]+=int(r['warranted'])
            patterns.setdefault(pattern,{a:0 for a in ARMS})[arm]+=int(r['warranted'])
            for stage,resp in (([('labels',pre)] if pre else [])+([('direct' if arm=='direct' else 'verdict',terminal)] if terminal['status']!='gated' else [])):
                u=usage.setdefault(stage,Counter());us=resp.get('usage',{})
                u.update({'issued':1,'length':int(us.get('done_reason')=='length'),'usage_available':int('eval_count' in us),
                          'generated_tokens':us.get('eval_count') or 0,'prompt_tokens':us.get('prompt_eval_count') or 0,'service_ns':us.get('total_duration') or 0})
                stages.setdefault(stage,Counter())[resp['status']]+=1
    paired={}
    by={(c['record'],c['arm']):c for c in cases}
    for metric in ('warranted','certified'):
        dd={k:[] for k in ('both','neither','direct_only','label_first_only')}
        for k in rows:
            x,y=(by[k,a][metric] for a in ARMS)
            cell='both' if x and y else 'direct_only' if x else 'label_first_only' if y else 'neither'
            dd[cell].append(k)
        paired[metric]=dd
    diffs=[v['label_first']-v['direct'] for v in families.values()]
    net=sum(diffs)
    summary=dict(totals=totals,by_family=families,by_pattern=patterns,paired=paired,stage_status=stages,usage=usage,
                 observed_net=net,missing_net_bounds=[net-totals['direct']['missing'],net+totals['label_first']['missing']],
                 layout_sign_flip_two_sided=reference(diffs),paid_api_usd=0)
    result=HERE/'results';save(result/'summary.json',summary)
    with (result/'cases.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(cases[0]));w.writeheader();w.writerows(cases)
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
