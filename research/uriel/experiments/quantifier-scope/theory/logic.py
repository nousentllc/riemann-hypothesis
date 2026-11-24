"""Finite behavioral predictions over the two-label domain, independent of the model scorer."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PATTERNS=('YY','NN','YN','NY')
OUTPUTS=('YY','YN','NY','NN')
ARMS=('any','both')

def signature(x,policy):
    first,last=x
    one='Y' if 'Y' in x else 'N'
    both='Y' if x=='YY' else 'N'
    return {'scope':one+both,'or_on_both':one*2,'and_on_both':both*2,'reversed':both+one,
            'always_yes':'YY','always_no':'NN','wording_only':'YN','first_row_twice':first*2,
            'second_row_twice':last*2}[policy]

POLICIES=('scope','or_on_both','and_on_both','reversed','always_yes','always_no','wording_only','first_row_twice','second_row_twice')

def matches(predicted, answers):
    return (int(answers==predicted),int(all(a=='?' or a==b for a,b in zip(answers,predicted))))

def sanity():
    for obs in map(''.join,product('YN?',repeat=2)):
        realized=[''.join(p) for p in product('YN',repeat=2) if all(a=='?' or a==v for a,v in zip(obs,p))]
        for prediction in OUTPUTS:
            yes=[int(z==prediction) for z in realized]
            assert matches(prediction,obs)==(min(yes),max(yes))
    tables={p:{x:signature(x,p) for x in PATTERNS} for p in POLICIES}
    distinguishes=[subset for k in range(1,5) for subset in combinations(PATTERNS,k)
                   if all(any(tables['scope'][v]!=tables[p][v] for v in subset) for p in POLICIES[1:])]
    m=min(map(len,distinguishes))
    space=list(product(OUTPUTS,repeat=4))
    assert len(space)==len(set(space))==256
    for k in range(5):
        for subset in combinations(range(4),k):
            target=tuple(tables['scope'][x] for x in PATTERNS)
            assert sum(all(t[i]==target[i] for i in subset) for t in space)==4**(4-k)
    assert tables['scope']=={'YY':'YY','NN':'NN','YN':'YN','NY':'YN'}
    return dict(pattern_order=PATTERNS,output_order=ARMS,truth_tables=tables,total_two_bit_maps=len(space),
                minimal_named_distinguishing_subsets=[s for s in distinguishes if len(s)==m],
                unrestricted_maps_compatible_after_k_distinct_rows=[4**(4-k) for k in range(5)])

def scores(rows,which):
    lower=upper=0
    for d in rows:
        a,b=matches(which[d['truth']],d['response'])
        lower+=a;upper+=b
    return dict(n=len(rows),matched=lower,possible=upper,mismatch=len(rows)-upper,undetermined=upper-lower)

def observations():
    records=json.loads((ROOT/'circuits/records.json').read_bytes())
    results=[]
    for rid,row in sorted(records.items()):
        order=row['survivors']
        truth=''.join('Y' if Fraction(row['states'][s]['target_current'])>Fraction(row['target_threshold']) else 'N' for s in order)
        path=ROOT/'pilot/observed'/rid
        label=json.loads((path/'labels/response.json').read_bytes())
        original=label['answer'];answers=[]
        for mode in ARMS:
            receipt=path/mode/'response.json'
            if original is None:
                assert not receipt.exists()
                answers.append('?')
            else:
                response=json.loads(receipt.read_bytes())['answer']
                answers.append(response['answer'] if response is not None else '?')
        out=''.join(answers)
        results.append(dict(record=rid,layout=row['family'],truth=truth,response=out,accurate_complete=bool(original)
                            and ''.join(original[i] for i in order)==truth and '?' not in out))
    return results

def score():
    design=sanity()
    obs=observations()
    groups={'all':obs,'mixed':[d for d in obs if len(set(d['truth']))==2],
            'accurate_complete':[d for d in obs if d['accurate_complete']],
            'mixed_accurate_complete':[d for d in obs if d['accurate_complete'] and len(set(d['truth']))==2]}
    named={p:{k:scores(v,design['truth_tables'][p]) for k,v in groups.items()} for p in POLICIES}
    grid=Counter()
    best=[];mx=-1
    for table in product(OUTPUTS,repeat=4):
        z=scores(obs,dict(zip(PATTERNS, table)))['matched']
        grid[z]+=1
        if z>mx:best=[];mx=z
        if z==mx:best.append(table)
    assert sum(grid.values())==256
    differences={}
    layouts=sorted({d['layout'] for d in obs})
    for f in layouts:
        options=[d['response'] for d in groups['mixed'] if d['layout']==f]
        assert len(options)==2
        differences[f]=options.count('YN')-options.count('YY')
    net=sum(differences.values())
    p=Fraction(sum(abs(sum(s*d for s,d in zip(sgn,differences.values())))>=abs(net)
                   for sgn in product((1,-1),repeat=6)),64)
    return dict(named=named,pattern_order=PATTERNS,best_matches=mx,best_maps=best,
                joint_score_histogram=dict(sorted(grid.items())),mixed_layout_net=differences,
                mixed_separation_minus_double_yes=net,fair_layout_sign_reference=str(p),records=obs)

def run():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('phase',choices=('design','results'));parser.add_argument('--write',action='store_true')
    a=parser.parse_args()
    r=sanity() if a.phase=='design' else score()
    out=ROOT/'theory'/('logic.json' if a.phase=='design' else 'policy_scores.json')
    content=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.write:out.write_text(content)
    elif out.read_text()!=content:raise ValueError('Archived calculation changed: '+out.name)
    print(out.name, r.get('minimal_named_distinguishing_subsets',r.get('mixed_layout_net')))
if __name__=='__main__':run()
