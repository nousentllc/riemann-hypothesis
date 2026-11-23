"""Exact continuous, fixed-first two-witness experiment. No external packages."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import json

LABELS=(4,8,9,10,11,12,32,63,64,80,99,120,143,144)
A,B=8,12
CLIPS=((12,8),(10,10),(11,9),(9,11))

def active(m,z):
    # z=x^2, no floating roots. m<floor(z) iff m+1<=z.
    return 1<=m and m+1<=z and z<m*m

def passes(es,z):
    return not any(active(m,z) for m in es)

def atoms(es,a,b,extra=()):
    coordinates={Q(a*a),Q(b*b),*map(Q,extra)}
    for m in es:
        coordinates.update((Q(m+1),Q(m*m)))
    events=sorted(z for z in coordinates if a*a<=z<=b*b)
    # Each value occurs once at an included event and once for each open cell.
    return sorted(events+[(x+y)/2 for x,y in zip(events,events[1:])])

def orient(es,fs,a,b):
    assert passes(es,a*a) and passes(fs,b*b) and a*a>b
    # Return squared coordinates. None denotes no left obstruction.
    large=[m for m in es if a*a<=m<b*b]
    small=[m for m in fs if a<m<=b]
    return (min(large)+1 if large else None, max(small,default=a)**2)

def witness_switch(states):
    # DP with free initial and terminal service, subject to every atom covered.
    costs=(0,0)
    inf=len(states)+2
    for left,right in states:
        prev=costs
        costs=(min(prev[0],prev[1]+1) if left else inf,
               min(prev[1],prev[0]+1) if right else inf)
    return None if min(costs)>=inf else min(costs)

def encoded(z):
    if z is None:return "no activation in target"
    k=isqrt(z)
    return str(k) if k*k==z else f"sqrt({z})"

def hand(es,fs,a,b):
    zs=atoms((*es,*fs),a,b)
    states=[(passes(es,z),passes(fs,z)) for z in zs]
    return dict(target=[a,b],left=list(es),right=list(fs),
                exterior=[passes(es,a*a),passes(fs,b*b)],
                covered=all(l or r for l,r in states),
                common_point=any(l and r for l,r in states),
                minimum_switches=witness_switch(states))

def main():
    lists=[frozenset(t) for n in range(3) for t in combinations(LABELS,n)]
    zs=atoms(LABELS,A,B,(d*d for clip in CLIPS for d in clip))
    full=(1<<len(zs))-1
    mask={e:sum(int(passes(e,z))<<i for i,z in enumerate(zs)) for e in lists}
    left_lists=[e for e in lists if mask[e]&1]
    right_lists=[e for e in lists if (mask[e]>>(len(zs)-1))&1]
    relevant=frozenset(m for m in LABELS if not all(passes([m],z) for z in zs))
    totals=Counter()
    clipcounts=[Counter() for _ in CLIPS]
    for e in left_lists:
        for f in right_lists:
            totals['anchored_pairs']+=1
            l,r=orient(e,f,A,B)
            actual=(mask[e]|mask[f])==full
            mono=all(bool(mask[e]&(1<<i))==(l is None or z<l) and
                     bool(mask[f]&(1<<i))==(r<=z) for i,z in enumerate(zs))
            assert mono and (l is None or r<=l)==actual
            totals['covered']+=int(actual)
            totals['one_witness_suffices']+=int(mask[e]==full or mask[f]==full)
            totals['covered_neither_alone']+=int(actual and mask[e]!=full and mask[f]!=full)
            totals['requires_handoff_without_shared_good_point']+=int(actual and not mask[e]&mask[f])
            totals['uncovered']+=int(not actual)
            totals['uncovered_equal_cardinality']+=int(not actual and len(e)==len(f))
            totals['uncovered_shared_label']+=int(not actual and bool(e&f))
            totals['covered_disjoint']+=int(actual and not e&f)
            totals['covered_disjoint_neither_alone']+=int(actual and not e&f and mask[e]!=full and mask[f]!=full)
            # Restricted order sufficient to extend one list throughout.
            # Only labels threatening the right endpoint have to be transported
            # from left list to right. Symmetrically for the left endpoint.
            right_danger={m for m in e if active(m,B*B)}
            left_danger={m for m in f if active(m,A*A)}
            ltransfer=right_danger.issubset(f)
            rtransfer=left_danger.issubset(e)
            assert ltransfer==(mask[e]==full)
            assert rtransfer==(mask[f]==full)
            requal=e&relevant==f&relevant
            assert not requal or (mask[e]==full and mask[f]==full)
            totals['identical_whole_lists']+=int(e==f)
            totals['identical_relevant_restrictions']+=int(requal)
            totals['left_low_subset_false_bridge']+=int(not actual and
                {m for m in e if m<A*A}.issubset({m for m in f if m<A*A}))
            for j,(cl,cr) in enumerate(CLIPS):
                lv=mask[e]&sum(1<<i for i,z in enumerate(zs) if z<=cl*cl)
                rv=mask[f]&sum(1<<i for i,z in enumerate(zs) if z>=cr*cr)
                end=min(cl*cl,l) if l is not None else cl*cl
                start=max(cr*cr,r)
                predicted=start<=end
                jointly=(lv|rv)==full
                assert predicted==jointly
                both_at_join=(start<end or start==end and (l is None or end<l))
                assert bool(lv&rv)==both_at_join
                c=clipcounts[j]
                c['covered']+=int(jointly)
                c['touch_only']+=int(jointly and end==start)
                c['covered_without_common_good_point']+=int(jointly and not lv&rv)
                c['clipping_loses_previously_covered']+=int(actual and not jointly)
    examples=[hand(*v,A,B) for v in [((80,),(11,)),((120,),(10,)),((99,),(10,)),
                                      ((4,80),(4,11)),((4,144),(8,)),((143,),(12,))]]
    for row in examples:
        l,r=orient(row['left'],row['right'],A,B)
        row['left_first_failure']=encoded(l)
        row['right_first_success']=encoded(r)
    three=hand((9,6888),(3,82),2,256)
    three['forced_points']={str(x):[tag for tag,e in [('L',(9,6888)),('R',(3,82))]
                                     if passes(e,x*x)] for x in (2,4,10,100)}
    assert three['minimum_switches']==3 and three['covered']
    return dict(model="two anchored scalar active-weight screens on closed availability domains",
                target=[A,B],Ct=2,eta=1,labels=LABELS,lists=len(lists),
                total_list_pairs=len(lists)**2,eligible_left=len(left_lists),
                eligible_right=len(right_lists),event_and_cell_representatives=len(zs),
                relevant_labels=sorted(relevant),unclipped=dict(sorted(totals.items())),
                clipped=[dict(left_end=x,right_start=y,**d) for (x,y),d in zip(CLIPS,clipcounts)],
                controls=examples,three_switch_control=three)
if __name__=='__main__':
    print(json.dumps(main(),indent=2))
