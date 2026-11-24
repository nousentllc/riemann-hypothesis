"""Independent case and family audit, including the exact missing-response bounds."""
import argparse
import csv
import hashlib
import itertools
import json
from collections import Counter
from datetime import datetime
from fractions import Fraction
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PILOT = ROOT / 'pilot'
ARMS = ('unmarked', 'marked', 'filtered')
COMPARISONS = tuple(itertools.combinations(ARMS, 2))


def read(path):
    return json.loads(path.read_bytes())


def check(test, message):
    if not test:
        raise ValueError(message)


def classify(ids, positive):
    signs = {item in positive for item in ids}
    if not signs:
        raise ValueError('Cannot infer a verdict from an empty set.')
    return 'U' if len(signs) == 2 else ('Y' if True in signs else 'N')


def oracle(row):
    states = row['states']
    pos = {sid for sid, state in states.items() if Fraction(state['target_current']) > Fraction(row['target_threshold'])}
    check(all(s['answer'] == (i in pos) for i, s in states.items()), 'Threshold disagreement')
    first = {i for i,s in states.items() if s['initial'] == row['initial_reading']}
    second = {i for i,s in states.items() if s['obs'][row['meter']] == row['reading']}
    ids = first & second
    check(len(ids)==2 and len(first)==len(second)==4 and set(row['survivors'])==ids, 'Intersection disagreement')
    check(classify(first,pos)==classify(second,pos)=='U', 'One meter shortcut')
    return ids, pos


def finite_pairs(left, right):
    table = Counter(zip(left, right))
    n = len(left)
    x, y = table[True, False], table[False, True]
    d = x+y
    p = min(Fraction(1), Fraction(2*sum(comb(d,i) for i in range(min(x,y)+1)), 2**d))
    return dict(n=n, left_only=x, right_only=y, both=table[True,True], neither=table[False,False],
                left_minus_right=x-y, exact_two_sided_p=str(p))


def possible_complete(items):
    """Each input is True, False, or None for an unobserved binary outcome."""
    return (int(all(i is True for i in items)), int(all(i is not False for i in items)))


def range_difference(left, right):
    return [sum(cell[0] for cell in left)-sum(cell[1] for cell in right),
            sum(cell[1] for cell in left)-sum(cell[0] for cell in right)]


def selftest():
    truth_space = (True, False, None)
    # Four binary outcomes, two each arm. Compare the analytical extrema with all completions.
    for slots in itertools.product(truth_space, repeat=4):
        unknown = [k for k, val in enumerate(slots) if val is None]
        diffs = []
        for bits in itertools.product((False,True),repeat=len(unknown)):
            data = list(slots)
            for i,b in zip(unknown,bits):
                data[i]=b
            diffs.append(int(all(data[:2]))-int(all(data[2:])))
        check(range_difference([possible_complete(slots[:2])],[possible_complete(slots[2:])]) ==
              [min(diffs),max(diffs)], 'Missing-data extremes')
    a,b=finite_pairs([True]*4+[False]*2,[False]*4+[False]*2),finite_pairs([True]*6,[True]*6)
    check(a['exact_two_sided_p']=='1/8' and b['exact_two_sided_p']=='1', 'Sign probabilities')


def score(row, receipt):
    surviving,positive = oracle(row)
    answer = None
    status = receipt['status']
    if status=='ok':
        check(receipt.get('usage',{}).get('done_reason')=='stop', 'Incomplete answer presented as completed')
        answer = json.loads(receipt['content'])
        check(isinstance(answer,dict) and set(answer)=={'verdict','certificate'}, 'Unexpected answer format')
        check(answer==receipt['answer'] and answer['verdict'] in ('Y','N','U'), 'Visible response and receipt disagree')
        ids=answer['certificate']
        check(isinstance(ids,list) and 1 <= len(ids) <= 8 and all(i in row['states'] for i in ids), 'Invalid certificate grammar')
    else:
        check(receipt.get('answer') is None, 'Non-terminal answer counted')
    items=answer['certificate'] if answer else []
    verdict=answer['verdict'] if answer else None
    submitted=set(items)
    warranted=classify(surviving,positive)
    exact=len(items)==2 and submitted==surviving
    pair=len(submitted)==len(items)==2
    return dict(verdict=verdict,expected=warranted,submitted=items,surviving=sorted(surviving),exact=exact,
                warranted=verdict==warranted,certified=exact and verdict==warranted,missing=answer is None,
                two_distinct=pair,coherent_pair=pair and classify(submitted,positive)==verdict,
                extra=sorted(submitted-surviving),omitted=sorted(surviving-submitted),
                unsupported_mixed=warranted=='U' and verdict in ('Y','N'))


def report():
    selftest()
    rows=read(ROOT/'circuits/records.json')
    with (PILOT/'results/cases.csv').open(newline='') as f:
        official=list(csv.DictReader(f))
    lookup={(s['record'],s['arm']):s for s in official}
    check(len(official)==len(lookup)==72, 'Incomplete official table')
    freeze=read(PILOT/'freeze.json')
    for name,h in freeze['sha256'].items():
        check(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==h, 'Drift '+name)
    jobs=read(PILOT/'order.json')
    dispatch={(j['record'],j['arm']):j['request_sha256'] for j in jobs}
    check(len(dispatch)==len(jobs)==72, 'Bad dispatch schedule')
    results={}
    timing={}
    for r,row in sorted(rows.items()):
        for a in ARMS:
            receipt=read(PILOT/'observed'/f'{r}_{a}'/'response.json')
            check(receipt['request_sha256']==dispatch[r,a], f'{r}/{a}: receipt outside frozen schedule')
            start,end=(datetime.fromisoformat(receipt[k]) for k in ('started','ended'))
            check(start<=end and start>=datetime.fromisoformat(freeze['at']), 'Unordered registration or timestamps')
            timing[r,a]=(start,end)
            val=score(row,receipt)
            result=lookup[r,a]
            for field,truth in [('certified',val['certified']),('sign',val['warranted']),('ids',val['exact'])]:
                check(str(truth).lower()==result[field].lower(), f'{r}/{a}: {field}')
            check((val['verdict'] or '')==result['verdict'] and val['expected']==result['expected'] and
                  val['submitted']==result['certificate'].split(), f'{r}/{a}: visible answer')
            results[r,a]=val
    fam=sorted({row['family'] for row in rows.values()})
    summaries={}
    for a in ARMS:
        values=[results[r,a] for r in rows]
        summaries[a]={k:sum(v[k] for v in values) for k in ['certified','exact','warranted','missing','two_distinct','coherent_pair','unsupported_mixed']}
        summaries[a]['inadmissible_among_two_distinct']=sum(v['two_distinct'] and bool(v['extra']) for v in values)
        summaries[a]['inadmissible_among_coherent_pairs']=sum(v['coherent_pair'] and bool(v['extra']) for v in values)
        summaries[a]['mixed_twins_both_U_but_incomplete']=0
        summaries[a]['mixed_twins_same_nonempty_ids']=0
        for f in fam:
            twins=[results[r,a] for r,v in rows.items() if v['family']==f and v['kind']=='ambiguous']
            check(len(twins)==2 and set(twins[0]['surviving']).isdisjoint(twins[1]['surviving']), 'Mixed twins')
            summaries[a]['mixed_twins_both_U_but_incomplete']+=int(all(v['verdict']=='U' for v in twins) and not all(v['exact'] for v in twins))
            x,y=(set(v['submitted']) for v in twins)
            summaries[a]['mixed_twins_same_nonempty_ids']+=int(bool(x) and x==y)
    contrasts={}
    for a,b in COMPARISONS:
        record=finite_pairs([results[r,a]['certified'] for r in rows],[results[r,b]['certified'] for r in rows])
        group={}
        for endpoint in ['decisive','ambiguous','all']:
            outcomes={arm:[] for arm in (a,b)}
            for f in fam:
                for arm in (a,b):
                    ids=[r for r,v in rows.items() if v['family']==f and endpoint in (v['kind'],'all')]
                    cell=[None if results[r,arm]['missing'] else results[r,arm]['certified'] for r in ids]
                    outcomes[arm].append(possible_complete(cell))
            paired=finite_pairs([bool(i[0]) for i in outcomes[a]],[bool(i[0]) for i in outcomes[b]])
            paired['missing_bounds_left_minus_right']=range_difference(outcomes[a],outcomes[b])
            group[endpoint]=paired
        contrasts[a+'_vs_'+b]=dict(records=record,layouts=group,
            left_only_records=[r for r in rows if results[r,a]['certified'] and not results[r,b]['certified']],
            right_only_records=[r for r in rows if results[r,b]['certified'] and not results[r,a]['certified']])
    ordered=[timing[j['record'],j['arm']] for j in jobs]
    check(all(x[1]<=y[0] for x,y in zip(ordered,ordered[1:])), 'Requests overlap or differ from the frozen order')
    elapsed=dict(first_request=ordered[0][0].isoformat(),last_response=ordered[-1][1].isoformat(),
                 elapsed_seconds=(ordered[-1][1]-ordered[0][0]).total_seconds(),
                 client_seconds={a:round(sum((timing[r,a][1]-timing[r,a][0]).total_seconds() for r in rows),6) for a in ARMS})
    reported=read(PILOT/'results/summary.json')
    for label,c in contrasts.items():
        a,b=label.split('_vs_')
        direct=label in reported['comparisons']
        other=reported['comparisons'][label if direct else b+'_vs_'+a]['complete_decisive']
        pair=c['layouts']['decisive']
        check(pair['both']==other['both'] and pair['neither']==other['neither']
              and pair['left_minus_right']==(1 if direct else -1)*other['net']
              and abs(float(Fraction(pair['exact_two_sided_p']))-other['two_sided_sign_p'])<1e-12,
              'Official paired table or probability differs')
        bounds=pair['missing_bounds_left_minus_right']
        check((bounds if direct else [-bounds[1],-bounds[0]])==other['missing_completion_net_bounds'],
              'Official missing-outcome bounds differ')
    report=dict(timing=elapsed,arms=summaries,matched=contrasts,cases={f'{r}_{a}':v for (r,a),v in results.items()})
    (ROOT/'audit/post.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'arms':summaries,'marked_vs_filtered':contrasts['marked_vs_filtered']},indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('test','post'))
    if parser.parse_args().action=='test':
        selftest()
        print('All 81 four-outcome missingness patterns and two conditional sign tests passed.')
    else:
        report()
