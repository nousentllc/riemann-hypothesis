"""Sharp transient-label test in exact power coordinates, without irrational comparisons."""
from fractions import Fraction as Q
from itertools import combinations
import json

def transitions(m,C,e):
    return (m+1)**e,m**C

def run_case(a,b,C,e,candidates):
    left,right=a**(C*e),b**(C*e)
    cut=(a**C).__floor__()
    bound=(b**e).__floor__()
    events={left,right}
    transient=[]
    masks={}
    for m in candidates:
        u,v=transitions(m,C,e)
        if left<=u<=right:events.add(u)
        if left<=v<=right:events.add(v)
        arc=left<u<v<=right
        integer=(cut<=m<=bound and (m+1)**e < m**C)
        assert arc==integer
        if arc:transient.append(m)
    ordered=sorted(events)
    points=sorted(ordered+[Q(u+v,2) for u,v in zip(ordered,ordered[1:])])
    for m in candidates:
        u,v=transitions(m,C,e)
        masks[m]=tuple(u<=z<v for z in points)
        bad=masks[m]
        # A left-passing singleton's bits can only turn from false to true.
        anchor_left=bad[0] or list(bad)==sorted(bad)
        # A right-passing singleton's bits can only turn from true to false.
        anchor_right=bad[-1] or list(bad)==sorted(bad,reverse=True)
        assert (m not in transient)==(anchor_left and anchor_right)
    # If all candidate singletons preserve the orientation then every subset
    # does for either endpoint it passes. Conversely a transient singleton suffices.
    small=tuple(candidates[:8])
    failure=False
    for size in range(len(small)+1):
        for subset in combinations(small,size):
            bad=[any(masks[m][i] for m in subset) for i in range(len(points))]
            o=(bad[0] or bad==sorted(bad)) and (bad[-1] or bad==sorted(bad,reverse=True))
            failure |= not o
    assert failure==bool(set(transient)&set(small))
    return dict(a=str(a),b=str(b),Ct=C,eta=e,strict=b**e<cut,transients=transient,
                strict_fails_but_oriented=not transient and not b**e<cut)

def main():
    points=[Q(1),Q(5,4),Q(3,2),Q(2),Q(5,2),Q(3),Q(4),Q(8),Q(12),Q(16)]
    cases=[run_case(a,b,C,e,tuple(range(1,129)))
           for C,e in [(2,1),(3,2),(4,3)] for a,b in combinations(points,2)]
    examples=[run_case(Q(5,4),Q(3,2),3,2,(1,2,3)),
              run_case(Q(2),Q(4),2,1,(4,)),
              run_case(Q(2),Q(16),2,1,(3,25))]
    return dict(cases=len(cases),candidate_labels=128,counts=dict(
        strict=sum(r['strict'] for r in cases),
        no_transients=sum(not r['transients'] for r in cases),
        crossover_false_no_transients=sum(r['strict_fails_but_oriented'] for r in cases),
        with_transients=sum(bool(r['transients']) for r in cases)),
        subset_window_pairs=len(cases)*256,examples=examples)
if __name__=='__main__':
    print(json.dumps(main(),indent=2))
