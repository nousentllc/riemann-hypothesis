"""Exact positive and negative controls for the original strict center predicate in Q_l."""
from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement
from math import floor
import json


@cache
def depth(p, z):
    b, power = 0, 1
    while power*p <= z:
        b += 1
        power *= p
    return b


def hits(p, center, z):
    modulus = p**(depth(p, z)+1)
    residue = center % modulus
    return frozenset([residue]) if 1 <= residue <= z else frozenset()


def transitions(p, maximum=32):
    # Every possible reduction of an integral Q_p center at the greatest precision.
    cap = p**(depth(p, maximum)+1)
    tally = dict(cases=0, unchanged=0, old_only=0, new_only=0, both_changed=0,
                 wrong_old_range=0, same_depth_restriction_mismatch=0)
    for s in range(cap):
        rows = [hits(p,s,z) for z in range(maximum+1)]
        for u,v in combinations_with_replacement(range(1,maximum+1),2):
            A,B=rows[u],rows[v]
            lost,added=A-B,B-A
            key = ("both_changed" if lost and added else "old_only" if lost
                   else "new_only" if added else "unchanged")
            tally[key]+=1
            tally["cases"]+=1
            small=frozenset(e for e in B if e<=u)
            tally["wrong_old_range"]+=int(bool(small-A))
            tally["same_depth_restriction_mismatch"]+=int(depth(p,u)==depth(p,v) and small!=A)
    assert tally["wrong_old_range"]==0 and tally["same_depth_restriction_mismatch"]==0
    assert tally["both_changed"] and tally["new_only"] and tally["old_only"]
    return dict(prime=p,reduction_classes=cap,maximum_cutoff=maximum,**tally)


def passes(E, x):
    return all(e <= x or not (1<=e<floor(x*x)) for e in E)


def obstructs(E, a, b):
    # There exists a real x in [a,b] with e+1<=x^2 and x<e iff these comparisons hold.
    return any(e>a and b*b>=e+1 and e*e>e+1 for e in E)


def fixed_gap(p, a, b, U=4, X=8):
    early,late=U**2,X**2
    n=p**(depth(p,late)+1)
    table=[(hits(p,s,early), hits(p,s,late)) for s in range(n)]
    same=[B for A,B in table if passes(A,a) and passes(B,b)]
    split=[B for A,_ in table if passes(A,a) for _,B in table if passes(B,b)]
    return dict(prime=p, endpoints=[str(a),str(b)],outer=[U,X],cutoffs=[early,late],
                center_classes=n, shared_passing=len(same),
                shared_hidden_holes=sum(obstructs(B,a,b) for B in same),
                independent_pairings=n*n, independent_passing=len(split),
                independent_hidden_holes=sum(obstructs(B,a,b) for B in split))


def main():
    a,b=Fraction(2),Fraction(4)
    eq=[fixed_gap(p,a,b) for p in (2,3,5,7)]
    strict=[fixed_gap(p,a,Fraction(7,2)) for p in (2,3,5,7)]
    assert all(r["shared_hidden_holes"]==0 and r["independent_hidden_holes"] for r in strict)
    assert all(r["shared_hidden_holes"] for r in eq)
    rollover=(hits(3,10,3),hits(3,10,10))
    assert rollover==(frozenset({1}),frozenset({10}))
    x=Fraction(5,2)
    # Nominate the target gap before the two center choices, then test its interior.
    assert passes(hits(2,7,16),a) and passes(hits(2,3,64),Fraction(7,2))
    assert not passes(hits(2,3,64),x)
    assert passes(hits(2,4,16),a) and passes(hits(2,4,64),b)
    assert not passes(hits(2,4,64),x)
    delays=[]
    for p in (2,3,5,7):
        for m in (8,32,128,512):
            label=3
            center=label+p**m
            cap=p**m
            before=hits(p,center,cap-1)
            at=hits(p,center,cap)
            assert label in before and label not in at
            delays.append(dict(prime=p,digits=m,weight=label,
                first_removal_cutoff=f"{p}^{m}",check_before=True,check_at=True))
    return dict(coherent_cutoff_transitions=[transitions(p) for p in (2,3,5,7)],
                strict_gap=strict,equality_gap=eq,
                controls=dict(rollover_3_10=[sorted(t) for t in rollover],
                    different_center_integer_pair=[7,3],different_center_interior_failure="5/2",
                    equality_shared_center=4,equality_interior_failure="5/2"),
                arbitrary_delay=delays)

if __name__=="__main__":
    print(json.dumps(main(),indent=2))
