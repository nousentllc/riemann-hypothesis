"""Exact finite controls for frozen-set interpolation. Run with Python 3."""
import json
from fractions import Fraction as F
from itertools import combinations

def fail_at(x, labels):
    count = x*x // 1
    return tuple(k for k in labels if 1 <= k < count and k > x)

def original_fail(x, labels):
    return tuple(k for k in labels if x < k <= x*x)

def main():
    axis = [F(i,4) for i in range(4,33)]
    sets = [s for n in range(9) for s in combinations(range(1,9),n)]
    counts = dict(families=len(sets), endpoint_pairs=0, passing_both=0, cross_condition=0,
                  fills=0, equal_cross_obstructed=0, below_cross_obstructed=0)
    for labels in sets:
        bad = [bool(fail_at(x,labels)) for x in axis]
        prefix=[0]
        for occupied in bad:
            prefix.append(prefix[-1]+occupied)
        for i,a in enumerate(axis):
            for j in range(i+1,len(axis)):
                b=axis[j]
                counts['endpoint_pairs']+=1
                if bad[i] or bad[j]:
                    continue
                counts['passing_both']+=1
                internal=prefix[j]-prefix[i+1]
                cutoff=a*a//1
                if cutoff>b:
                    counts['cross_condition']+=1
                    assert internal==0, (labels,a,b)
                    counts['fills']+=1
                elif internal:
                    key='equal_cross_obstructed' if cutoff==b else 'below_cross_obstructed'
                    counts[key]+=1
    cluster={str(x):dict(raw=original_fail(x,[9,16]),active=fail_at(x,[9,16]))
             for x in (F(3),F(4),F(9),F(16))}
    assert not fail_at(F(2),[4]) and fail_at(F(5,2),[4]) == (4,) and not fail_at(F(4),[4])
    assert not fail_at(F(3),[9,16]) and fail_at(F(4),[9,16]) == (9,)
    assert fail_at(F(9),[9,16]) == (16,) and not fail_at(F(16),[9,16])
    assert counts['equal_cross_obstructed']>0 and counts['below_cross_obstructed']>0
    print(json.dumps(dict(exponents=dict(Ct=2,eta=1),axis="1 through 8, step 1/4",counts=counts,
        overlap_labels=[9,16],overlap_control=cluster,
        equality_example=dict(labels=[4],a="2",x="5/2",b="4")),indent=2))
if __name__=='__main__':
    main()
