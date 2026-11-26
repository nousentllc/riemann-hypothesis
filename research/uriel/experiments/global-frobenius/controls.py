"""Exact finite controls for dyadic cosets and disjoint Bernoulli triples."""

from collections import Counter
from fractions import Fraction
from math import comb, gcd
from itertools import combinations
import json


def dyadic_construct(n, mask):
    points = [i for i in range(n) if (mask >> i) & 1]
    if len(points) < 3:
        return None
    a = points[0]
    span_step = gcd(n, *(b-a for b in points))
    order = n // span_step
    c = {(b-a)//span_step: b for b in points}
    even = [j for j in c if j % 2 == 0]
    odd = [j for j in c if j % 2]
    if len(even) >= 2:
        anchor = odd[0]
        targets = even[:2]
    else:
        anchor = even[0]
        targets = odd[:2]
    i, j = [(b-anchor) % order for b in targets]
    assert 0 < i < order and 0 < j < order and i % 2 and j % 2 and i != j
    assert order >= len(points)
    assert all((c[anchor] + e*span_step) % n in points for e in (i,j))
    step = (i * span_step) % n
    j_unit = (j * pow(i,-1,order)) % order
    assert j_unit % 2 and j_unit != 1
    assert (c[anchor]+step) % n in points and (c[anchor]+j_unit*step) % n in points
    return (span_step, order, c[anchor], i, j)


def full_ray_bruteforce(n, mask):
    for h in range(1,n):
        order = n // gcd(n,h)
        for t in range(n):
            if (mask >> t) & 1:
                degree = sum((mask >> ((t+i*h)%n)) & 1 for i in range(1,order,2))
                if degree >= 2:
                    return True
    return False


def short_masks(n):
    return sorted({
        (1 << t) | (1 << ((t+h)%n)) | (1 << ((t+3*h)%n))
        for h in range(1,n) if n // gcd(n,h) >= 4 for t in range(n)
    })


def enumerate_cycles():
    rows = []
    for n in (4,8,16):
        short = short_masks(n)
        classes = Counter()
        max_gap = 0
        largest = None
        for mask in range(1 << n):
            size = bin(mask).count('1')
            full = dyadic_construct(n,mask)
            if n <= 8:
                assert bool(full) == full_ray_bruteforce(n,mask)
            short_ok = any(mask & t == t for t in short)
            if short_ok:
                assert full
            if full and not short_ok:
                classes['full_but_no_1_3'] += 1
                if size > max_gap:
                    max_gap,size_mask = size,mask
                    largest = [i for i in range(n) if (size_mask >> i)&1]
            elif full:
                classes['short_and_full'] += 1
            else:
                classes['no_full'] += 1
        rows.append({'n':n, 'masks':1 << n,'distinct_1_3_triples':len(short),
                     'classes':dict(classes),'largest_full_without_short':largest})
    return rows


def mixed_cosets():
    subgroup_n, cosets = 4,3
    n = subgroup_n * cosets
    successes = Counter()
    for mask in range(1 << n):
        parts = [(mask >> (i*subgroup_n)) & ((1 << subgroup_n)-1) for i in range(cosets)]
        c = any(dyadic_construct(subgroup_n,p) for p in parts)
        size = bin(mask).count('1')
        successes['success'] += int(c)
        if size > 2*cosets:
            assert c
            successes['above_2o'] += 1
    return {'n':n,'cosets':cosets,'masks':1<<n,'counts':dict(successes)}


def block_counts(m, delta):
    p = (Fraction(3,4)*delta)**3
    d = [Fraction(1)]
    for _ in range(m):
        d = [x+y for x,y in zip([x*(1-p) for x in d]+[0],[0]+[p*x for x in d])]
    mean=m*p
    variance=m*p*(1-p)
    assert sum(d)==1
    assert sum(i*x for i,x in enumerate(d))==mean
    assert sum((i-mean)**2*x for i,x in enumerate(d))==variance
    failure=sum(x for i,x in enumerate(d) if i < mean/2)
    assert failure <= min(Fraction(1), 4/mean)
    return {'blocks':m,'delta':str(delta),'expectation':str(mean),
            'failure_decimal':round(float(failure),10),'failure_exact':str(failure)}


def incidence_check(n, selected, threshold):
    order = lambda shift: n // gcd(n, shift % n)
    bad_steps = {h for h in range(n) if order(h) < threshold}
    witnesses = Counter()
    triples = 0
    for pts in combinations(sorted(selected),3):
        if any((b-a) % n in bad_steps for a,b in combinations(pts,2)):
            continue
        triples += 1
        feasible = []
        for anchor in pts:
            targets = sorted(set(pts)-{anchor})
            h = (targets[0]-anchor) % n
            u = (targets[1]-anchor) % n
            if order(h) != order(u):
                continue
            d = gcd(n,h)
            m = n//d
            j = ((u//d)*pow(h//d,-1,m)) % m
            assert j % 2 == 1 and 1 < j < m
            assert (anchor+j*h) % n == targets[1]
            feasible.append((h,anchor))
        assert feasible
        witnesses[min(feasible)] += 1
    m = len(selected)
    b = len(bad_steps)
    assert triples * 6 >= m * max(m-b,0) * max(m-2*b,0)
    assert all(v <= m for v in witnesses.values())
    assert len(witnesses) * m >= triples
    if m >= 4*b:
        assert 24*len(witnesses) >= m*m
    return {'order':n,'retained':m,'long_threshold':threshold,'small_steps':b,
            'long_triples':triples,'certified_incidences':len(witnesses),
            'max_fiber':max(witnesses.values(),default=0)}


def tree_incidence(points, order, threshold):
    if order < max(2, threshold) or len(points) < 3:
        return 0
    left = [p//2 for p in points if p%2==0]
    right = [p//2 for p in points if p%2==1]
    u, v = len(left), len(right)
    local = (order//2) * (u*int(v>=2) + v*int(u>=2))
    return local + tree_incidence(left,order//2,threshold) + tree_incidence(right,order//2,threshold)


def brute_incidence(points, n, threshold):
    total = 0
    for h in range(1,n):
        order = n//gcd(n,h)
        if order >= threshold:
            for t in points:
                degree = sum((t+i*h)%n in points for i in range(1,order,2))
                total += int(degree>=2)
    return total


def tree_controls():
    panels = []
    for n, thresholds in [(4,(2,4,5)),(8,(2,4,5,9)),(16,(2,5,9,17))]:
        for threshold in thresholds:
            b = sum(n//gcd(n,h) < threshold for h in range(n))
            null = 0
            maximum = 0
            for mask in range(1<<n):
                selected = {j for j in range(n) if (mask>>j)&1}
                predicted = tree_incidence(selected,n,threshold)
                if n <= 8 or mask % 257 == 0:
                    assert predicted == brute_incidence(selected,n,threshold)
                absent = len(selected)<=2 or len({j%(n//b) for j in selected})<=1
                assert (predicted==0)==absent
                null += int(absent)
                if absent:
                    maximum = max(maximum,len(selected))
            formula = 1+n+comb(n,2)+(n//b)*((1<<b)-1-b-comb(b,2))
            assert null == formula and maximum == max(2,b)
            panels.append({'order':n,'threshold':threshold,'short_subgroup_size':b,
                           'zero_incidence_masks':null,'largest_zero_incidence_mask':maximum})
    for n, selected, threshold in [(16,set(range(16)),4),
                                   (32,{i for i in range(32) if i%3!=0},5),
                                   (64,{i for i in range(64) if i%5<3},8)]:
        total = tree_incidence(selected,n,threshold)
        assert total == brute_incidence(selected,n,threshold)
        panels.append({'order':n,'threshold':threshold,'retained':len(selected),
                       'all_long_incidences':total})
    return panels


def main():
    print(json.dumps({'cycles':enumerate_cycles(),'mixed_cosets':mixed_cosets(),
                      'incidences':[incidence_check(n,T,b) for n,T,b in
                         [(16,set(range(16)),4),
                          (32,{i for i in range(32) if i%3!=0},5),
                          (64,{i for i in range(64) if i%5<3},8)]],
                      'dyadic_tree':tree_controls(),
                      'bernoulli_blocks':[block_counts(m,Fraction(1,2)) for m in (16,64,128)]},
                     indent=2))


if __name__ == '__main__':
    main()
