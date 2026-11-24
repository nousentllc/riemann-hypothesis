"""Score a registered run, including all scheduled missing sessions."""
import argparse
from collections import Counter,defaultdict
import csv
import json
from math import comb
from pathlib import Path
from domain import HERE, ARMS, save, score_session
from run import check_manifest

def prob_le(k,n,p):
    return sum(comb(n,i)*p**i*(1-p)**(n-i) for i in range(k+1))

def solve_decreasing(k,n,alpha):
    lo,hi=0.,1.
    for _ in range(70):
        mid=(lo+hi)/2
        if prob_le(k,n,mid)>alpha: lo=mid
        else: hi=mid
    return (lo+hi)/2

def paired(w,l):
    n=w+l
    if not n: return {'discordant':0,'two_sided_sign_p':1,'conditional_win_95pct':None}
    lower=0 if w==0 else solve_decreasing(w-1,n,.975)
    upper=1 if w==n else solve_decreasing(w,n,.025)
    return dict(discordant=n,two_sided_sign_p=min(1,2*prob_le(min(w,l),n,.5)),conditional_win_95pct=[lower,upper])

def analyze(part,model):
    folder,reg=check_manifest(part,model,False)
    rows=json.loads((folder/'records.json').read_text()); jobs=json.loads((folder/'order.json').read_text())
    base=HERE/'observed'/(part+'-'+model)
    totals={a:Counter() for a in ARMS}; families=defaultdict(dict); output=[]
    for job in jobs:
        rid,arm=job['record'],job['arm']; row=rows[rid]; path=base/(rid+'_'+arm)/'session.json'
        receipt=json.loads(path.read_text()) if path.is_file() else {}
        s=score_session(row,receipt)
        case=dict(domain=row['domain'],family=row['family'],variant=row['variant'],record=rid,arm=arm,
            kind=s['kind'],target=s['target'],initial=s['initial']['verdict'],initial_licensed=s['initial']['licensed'],
            initial_expected=s['initial']['expected'],initial_certified=s['initial']['certified'],
            initial_guessed=s['initial']['guessed'],initial_wrong_sign=s['initial']['wrong_sign'],
            initial_unnecessary_abstention=s['unnecessary_initial_abstention'],lookup=s['used'],
            productive=s['productive'],final=s['final']['verdict'],final_expected_seen=s['final']['expected'],
            final_licensed_seen=s['final']['licensed'],final_guessed=s['final']['guessed'],
            final_wrong_sign=s['final']['wrong_sign'],final_certified_seen=s['final']['certified'],
            missed_resolvable=s['missed_resolvable'],unsupported=s['unsupported'],success=s['pass_case'])
        families[row['domain'],row['family']].setdefault(arm,[]).append(s['pass_case'])
        c=totals[arm]; c['sessions']+=1; c['recorded']+=int(bool(receipt))
        c['parseable_final']+=int(s['final']['verdict'] is not None)
        c['certified_cases']+=int(s['pass_case']); c['unsupported']+=s['unsupported']
        c['certified_determinate']+=int(s['target']!='U' and s['pass_case'])
        c['missed_resolvable']+=int(s['missed_resolvable'])
        c['right_final_without_valid_certificate']+=int(s['final']['verdict']==s['target'] and not s['pass_case'])
        c['used_lookup']+=int(s['used'] in row['menu'])
        c['productive_lookups']+=int(s['productive']); c['missed_opportunity']+=int(s['kind']=='lookup' and not s['productive'])
        c['unnecessary_initial_abstention']+=int(s['unnecessary_initial_abstention'])
        c['attainable_final_verdict']+=int(s['final']['verdict']==s['target'])
        for stage in ['first','second']:
            if stage not in receipt:continue
            t=receipt[stage]; usage=t.get('usage',{})
            c['calls']+=1; c['prompt_tokens']+=usage.get('prompt_eval_count') or 0
            c['generated_tokens']+=usage.get('eval_count') or 0
            c['service_nanoseconds']+=usage.get('total_duration') or 0
            c['unfinished_calls']+=int(t.get('status')!='ok')
        output.append(case)
    by_domain=defaultdict(Counter); by_family=[]; wins=losses=0
    for (domain,family),arms in sorted(families.items()):
        g,m=(all(arms[a]) for a in ARMS)
        by_domain[domain]['general']+=int(g); by_domain[domain]['method']+=int(m)
        by_domain[domain]['gain']+=int(m)-int(g)
        wins+=int(m and not g); losses+=int(g and not m)
        by_family.append(dict(domain=domain,family=family,general=g,method=m))
    out=dict(registry=folder.name,totals=totals,by_domain=by_domain,families=by_family,method_wins=wins,
             method_losses=losses,ties=len(families)-wins-losses,paired=paired(wins,losses),direct_api_usd=0)
    if part=='test':
        out['advance']=all(c['gain']>=1 for c in by_domain.values()) and totals['method']['unsupported']<=totals['general']['unsupported'] and totals['method']['certified_determinate']>=totals['general']['certified_determinate']
    outdir=HERE/'reports'/folder.name; save(outdir/'summary.json',out)
    with (outdir/'cases.csv').open('w',newline='') as fp:
        writer=csv.DictWriter(fp,fieldnames=list(output[0]));writer.writeheader();writer.writerows(output)
    print(json.dumps(out,indent=2))
    return out,output

def decide(model):
    result,cases=analyze('dev',model)
    if any(s['recorded']!=s['sessions'] for s in result['totals'].values()): raise ValueError('Development incomplete')
    floor=any(not any(c['final'] for c in cases if c['arm']==arm and c['domain']==domain)
              for arm in ARMS for domain in ('formal','circuits')) or not any(c['success'] for c in cases)
    ceiling=all(c['success'] for c in cases)
    selected=('gptoss' if model=='qwen' else None) if floor else model
    decision=dict(attempted=model,selected=selected,development_floor=floor,
        development_ceiling=ceiling,ready_for_scored_run=not floor and selected==model)
    save(HERE/('development_'+model+'.json'),decision)
    if decision['ready_for_scored_run']:save(HERE/'development_decision.json',decision)
    print(json.dumps(decision))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('kind',choices=['dev','test','decide'])
    parser.add_argument('model',choices=['qwen','gptoss'])
    args=parser.parse_args()
    if args.kind=='decide': decide(args.model)
    else: analyze(args.kind,args.model)
