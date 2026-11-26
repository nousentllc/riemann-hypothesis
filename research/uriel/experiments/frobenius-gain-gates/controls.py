"""Deterministic finite controls for the original-orbit gain audit."""

from collections import Counter
from fractions import Fraction as Q
from math import gcd
import json


def oriented_tree(n, b, preference=0):
    """Represent a node by (even child, odd child), with leaves holding positions."""
    index = 0

    def split(points):
        nonlocal index
        if len(points) == b:
            return tuple(points)
        i = index
        index += 1
        left, right = split(points[::2]), split(points[1::2])
        return (right, left) if preference >> i & 1 else (left, right)

    return split(list(range(n)))


def census(tree, b, mask):
    if len(tree) == b and isinstance(tree[0], int):
        return sum(mask >> i & 1 for i in tree), 0, 0
    u, marks_l, depth_l = census(tree[0], b, mask)
    v, marks_r, depth_r = census(tree[1], b, mask)
    return u + v, marks_l + marks_r + (u*v if u >= 2 else 0), 1 + max(depth_l, depth_r)


def origins(tree, b):
    if len(tree) == b and isinstance(tree[0], int):
        yield from tree
    else:
        yield from origins(tree[0], b)
        yield from origins(tree[1], b)


def brute(n, b, mask, index_order):
    points = {i for i in range(n) if mask >> i & 1}
    found = set()
    for t in points:
        for h in range(1, n):
            q = n//gcd(n,h)
            if q <= b or (t+h)%n not in points:
                continue
            orbit = [(t+i*h)%n for i in range(q)]
            origin = min(orbit, key=index_order.__getitem__)
            if orbit.index(origin)%2 != 1:
                continue
            if any(orbit[e] in points for e in range(3,q,2)):
                found.add((t,h))
    return found


def cycle_panels():
    results = []
    for n,b,orientations in [(4,1,8),(8,1,128),(8,2,8),(16,1,1),(16,4,1)]:
        maximum_null = 0
        head_counts = Counter()
        tested = 0
        for o in range(orientations):
            tree = oriented_tree(n,b,o)
            index_order = {p: i for i,p in enumerate(origins(tree,b))}
            assert len(index_order) == n
            for mask in range(1<<n):
                size, found, depth = census(tree,b,mask)
                assert size*size <= 2*found + (b+2*depth)*size
                if n<=8 or mask%257==0:
                    assert found==len(brute(n,b,mask,index_order))
                    tested += 1
                if o==0:
                    head_counts[found] += 1
                if found==0:
                    maximum_null=max(maximum_null,size)
            assert census(tree,b,(1<<n)-1)[1]==len(brute(n,b,(1<<n)-1,index_order))
        assert maximum_null==b+depth
        results.append({'order':n,'leaf_capacity':b,'depth':depth,'orientations':orientations,
                        'masks_per_orientation':1<<n,'direct_checks':tested,
                        'largest_null_mask':maximum_null,'canonical_null_masks':head_counts[0],
                        'full_mask_adjacent_incidences':max(head_counts)})
    return results


def denominator_and_price_checks():
    y, bprime, p, width = Q(1024), Q(1000), 503, Q(3,8)
    cap = Q(1100)
    supply = y*bprime
    assert (Q(3,2)*y < p*p and p < y/2 and p**3>=2*y)
    for i in range(1,11):
        assert not y*(1-width)<=p**i<=y*(1+width)
    values = []
    for i in [1,3,5]:
        value=supply/p**i
        residual=max(Q(0),value-cap)
        minimum=min(value,cap)
        assert residual+minimum==value
        assert (residual>0)==(i==1)
        values.append({'offset':i,'supply':str(value),'residual':str(residual),'minimum':str(minimum)})
    credit = max(Q(0),supply/p-cap)
    cases = []
    for g0 in (Q(100),Q(-90)):
        for price in (Q(100),Q(credit+50)):
            raw = g0+credit-price
            premium=max(Q(0),raw-max(g0,0))
            assert (premium>0)==(price==100)
            cases.append({'fallback_raw':str(g0),'price':str(price),'clipped_premium':str(premium)})
    return {'y':str(y),'p':p,'capacity':str(cap),'rows':values,'price_controls':cases}


def ramp_panel():
    y = Q(2**15)
    def kernel(n):
        return max(Q(0),1/Q(n)-2/y)-max(Q(0),1/Q(n)-3/y)
    nonzero = 0
    flat = 0
    for n in range(1,int(y)+1):
        k = kernel(n)
        assert 0 <= k <= min(1/y,1/Q(n))
        assert (k>0)==(n<y/2)
        assert (k==1/y)==(n<=y/3)
        nonzero += int(k>0)
        flat += int(k==1/y)
    return {'y':int(y),'integer_inputs':int(y),'positive_kernel_inputs':nonzero,'flat_kernel_inputs':flat}


def main():
    print(json.dumps({'oriented_census':cycle_panels(),'interior_and_price':denominator_and_price_checks(),
                      'normalized_ramp':ramp_panel()},indent=2))


if __name__=='__main__':
    main()
