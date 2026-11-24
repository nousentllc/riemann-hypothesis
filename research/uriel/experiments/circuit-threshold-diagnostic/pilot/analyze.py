"""Score achieved and attainable decisions, with one independent primary pair per layout."""
import csv
import json
from collections import Counter
from pathlib import Path

from exact import paired
from instrument import HERE, oracle, score_session, save
from run import ARMS, RECORDS, verify_frozen


def collect():
    verify_frozen()
    rows=json.loads(RECORDS.read_text())
    cases=[]; totals={a:Counter() for a in ARMS}
    for job in json.loads((HERE/'order.json').read_text()):
        rid,arm=job['record'],job['arm']; row=rows[rid]
        receipt=json.loads((HERE/'observed'/f'{rid}_{arm}'/'session.json').read_text())
        if (receipt['record'],receipt['arm'])!=(rid,arm):
            raise ValueError('Mismatched receipt')
        s=score_session(row,receipt); first=s['initial']; final=s['final']; k=s['kind']
        if s['pass_case']:
            barrier='pass'
        elif k=='lookup' and not s['productive']:
            barrier='wrong meter' if s['used'] in row['menu'] else 'no usable request'
        elif final['verdict']!=s['target']:
            barrier='decision or missing'
        else:
            barrier='certificate'
        observation=receipt.get('observation',{})
        needed=oracle(row)['guaranteed'] if k=='lookup' else []
        case=dict(record=rid,family=row['family'],variant=row['variant'],arm=arm,kind=k,target=s['target'],
            initial=first['verdict'],initial_warrant=first['expected'],initial_licensed=first['licensed'],
            initial_certified=first['certified'],initial_unsupported=first['unsupported'],lookup=s['used'],
            decisive_meter=''.join(needed),returned=observation.get('value'),productive=s['productive'],
            final=final['verdict'],final_warrant=final['expected'],final_certified=final['certified'],
            success=s['pass_case'],unsupported=s['unsupported'],first_failure=barrier)
        cases.append(case)
        c=totals[arm]
        c.update(dict(sessions=1,productive=int(s['productive']),actionable_certified=int(k=='lookup' and s['pass_case']),
            certified=int(s['pass_case']),unsupported=s['unsupported'],initial_certified=int(first['certified']),
            initial_licensed=int(first['licensed']),used_lookup=int(s['used'] in row['menu']),
            unnecessary_lookup_settled=int(k=='settled' and s['used'] in row['menu']),
            attainable_final_sign=int(final['verdict']==s['target']),parseable_final=int(final['verdict'] is not None)))
        for st in ('first','second'):
            if st not in receipt:
                continue
            t=receipt[st]; u=t.get('usage',{})
            c.update(dict(calls=1,invalid_calls=int(t.get('status')!='ok'),length_limited=int(u.get('done_reason')=='length'),
                generated_tokens=u.get('eval_count') or 0,prompt_tokens=u.get('prompt_eval_count') or 0,
                service_ns=u.get('total_duration') or 0))
    return cases,totals


def contrast(cases, metric, kind=None):
    pairs={}
    for row in cases:
        if kind is None or row['kind']==kind:
            pairs.setdefault(row['record'],{})[row['arm']]=bool(row[metric])
    counts=Counter((r['raw'],r['labeled']) for r in pairs.values())
    wins=counts[False,True];losses=counts[True,False]
    return dict(n=len(pairs),both=counts[True,True],neither=counts[False,False],labeled_only=wins,
                raw_only=losses,net=wins-losses,**paired(wins,losses))


def main():
    cases,t=collect()
    if len(cases)!=24:
        raise ValueError('Incomplete schedule')
    primary=contrast(cases,'productive','lookup')
    second=contrast(cases,'success','lookup')
    strata={}
    for a in ARMS:
        strata[a]={}
        for kind in ('lookup','settled','ambiguous'):
            group=[c for c in cases if c['arm']==a and c['kind']==kind]
            strata[a][kind]=dict(n=len(group),certified=sum(c['success'] for c in group),
                initial_certified=sum(c['initial_certified'] for c in group),unsupported=sum(c['unsupported'] for c in group),
                productive=sum(c['productive'] for c in group),first_barrier=dict(Counter(c['first_failure'] for c in group)))
        families={c['family'] for c in cases}
        t[a]['complete_families']=sum(all(c['success'] for c in cases if c['family']==f and c['arm']==a) for f in families)
    result=dict(totals=t,primary=primary,actionable_secondary=second,strata=strata,paid_api_usd=0,
                development_signal=primary['net']>=2 and second['net']>=1)
    folder=HERE/'results';save(folder/'summary.json',result)
    with (folder/'cases.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(cases[0]));w.writeheader()
        w.writerows(sorted(cases,key=lambda r:(r['record'],ARMS.index(r['arm']))))
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
