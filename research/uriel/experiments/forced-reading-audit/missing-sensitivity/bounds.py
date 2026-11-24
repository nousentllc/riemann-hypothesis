"""Exact joint support of the registered development criteria given missing decisions."""
import argparse
from collections import Counter, defaultdict
import csv
from itertools import product
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUTCOMES=((0,0),(1,0),(1,1))
AXES=('net_complete_decisive_families','net_exact_decisive_ID_sets','net_certified_ambiguous_controls')


def bit(value):
    if value in ('True',True): return 1
    if value in ('False',False): return 0
    raise ValueError(f'Expected a Boolean score, received {value!r}')


def alternatives(row):
    fixed=(bit(row['ids']),bit(row['certified']))
    if fixed not in OUTCOMES: raise ValueError('A joint certificate requires exact IDs')
    if row['status']=='ok':
        if row['verdict'] not in ('U','Y','N'):raise ValueError('Accepted answer lacks a verdict')
        return (fixed,)
    if row['status'] not in ('invalid','error','interrupted') or row['verdict'] not in ('',None) or fixed!=(0,0):
        raise ValueError('Unrecognized missing-status or nonzero missing score')
    return OUTCOMES


def validate(layout):
    if len(layout)!=6: raise ValueError('Expected six sessions per layout')
    for arm in ('full','filtered'):
        kinds=Counter(r['kind'] for r in layout if r['arm']==arm)
        if kinds!=dict(decisive=2,ambiguous=1): raise ValueError('Layout lacks a complete arm')
    ids0={(r['record'],r['kind']) for r in layout if r['arm']=='full'}
    ids1={(r['record'],r['kind']) for r in layout if r['arm']=='filtered'}
    if len(ids0)!=3 or ids0!=ids1: raise ValueError('Arms do not cover three matched records')


def contributions(rows, selections):
    arm_counts={}
    for arm in ('full','filtered'):
        dec=[(i,c) for r,(i,c) in zip(rows,selections) if r['arm']==arm and r['kind']=='decisive']
        amb=next(c for r,(_,c) in zip(rows,selections) if r['arm']==arm and r['kind']=='ambiguous')
        arm_counts[arm]=(int(all(c for _,c in dec)),sum(i for i,_ in dec),amb)
    return tuple(f-u for f,u in zip(arm_counts['filtered'],arm_counts['full']))


def add(left,right):
    return tuple(a+b for a,b in zip(left,right))


def gate(triple):
    family,ids,controls=triple
    return family>=2 and ids>=2 and controls>=0


def analyze(rows):
    grouped=defaultdict(list); missing={'full':Counter(),'filtered':Counter()}
    for r in rows:
        if r['arm'] not in missing: raise ValueError(f"Invalid view {r['arm']}")
        grouped[r['family']].append(r)
        if r['status']!='ok':missing[r['arm']][r['status']]+=1
    if not grouped: raise ValueError('No cases supplied')
    total=Counter({(0,0,0):1}); bounds=[[0]*3 for _ in range(3)]
    for layout in grouped.values():
        validate(layout);opts=[alternatives(r) for r in layout]
        local=Counter(contributions(layout,values) for values in product(*opts))
        new=Counter()
        for prior,count in total.items():
            for delta,local_count in local.items():
                new[add(prior,delta)]+=count*local_count
        total=new
        # Independently realize registered, least-favorable and most-favorable worlds.
        for j in range(3):
            choices=[m[-1] if (j==1 and r['arm']=='full' or j==2 and r['arm']=='filtered') else m[0]
                     for r,m in zip(layout,opts)]
            bounds[j]=list(add(bounds[j],contributions(layout,choices)))
    m=sum(sum(by_status.values()) for by_status in missing.values())
    if sum(total.values())!=3**m: raise ValueError('Missing or duplicate completion assignment')
    original,lowest,highest=map(tuple,bounds)
    sharp={name:[min(v[i] for v in total),max(v[i] for v in total)] for i,name in enumerate(AXES)}
    if any(sharp[k]!=[l,h] for k,l,h in zip(AXES,lowest,highest)):
        raise ValueError('Extreme-assignment and enumeration bounds disagree')
    gates=sorted({gate(t) for t in total})
    if gates!=sorted({gate(lowest),gate(highest)}): raise ValueError('Joint gate check disagrees')
    return dict(method='Missing-session equivalence classes enumerated jointly per layout; no probability weighting.',
        records_per_arm=len(rows)//2,distinct_layouts=len(grouped),
        missing_sessions={a:sum(c.values()) for a,c in missing.items()},missing_status_counts=missing,
        possible_endpoint_class_assignments=3**m,possible_distinct_endpoint_triples=len(total),
        registered_values=dict(zip(AXES,original)),registered_gate=gate(original),sharp_ranges=sharp,
        attainable_gate_outcomes=gates,can_change_registered_gate=len(gates)==2,
        joint_extremes=dict(worst_for_filtered=dict(zip(AXES,lowest)),best_for_filtered=dict(zip(AXES,highest))),
        class_assignments_passing_gate=sum(c for t,c in total.items() if gate(t)),
        class_assignments_failing_gate=sum(c for t,c in total.items() if not gate(t)),
        note='Counts refer to possible classes of score patterns. Their frequencies are combinatorial and do not estimate probabilities.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',type=Path,default=HERE.parent/'pilot/results/cases.csv')
    parser.add_argument('--write',action='store_true',help='Store release results; absent this switch, verify the archived report.')
    args=parser.parse_args()
    with args.cases.open(newline='') as f: rows=list(csv.DictReader(f))
    if len(rows)!=36 or len({r['family'] for r in rows})!=6:raise ValueError('Incomplete scored release')
    result=analyze(rows)
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    dst=HERE/'results.json'
    if args.write:dst.write_text(output)
    elif dst.read_text()!=output:raise ValueError('Archived sensitivity report differs')
    print(output)


if __name__=='__main__':main()
