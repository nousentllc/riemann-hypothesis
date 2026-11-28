"""Exhaust canonical orderings in the root-odd subtree of the 32-class support."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, perm
from pathlib import Path
import json

Q = F(119, 50)
ALL = (1 << 16) - 1


def indices(mask):
    return [j for j in range(16) if mask & (1 << j)]


def congruence(stride, residue):
    return sum(1 << k for k in range(residue, 16, stride))


NODES = [(s, i, congruence(2*s, i), congruence(2*s, s+i))
         for s in (1, 2, 4, 8) for i in range(s)]


def exp_bounds(x):
    term, low = F(1), F(1)
    for j in range(1, 29):
        term *= x/j
        low += term
    return low, low + term*x/29/(1-x/30)


@lru_cache(None)
def tile(mu, nu):
    # One test bounds the geometric cell factor for every integer r >= 2.
    lo, hi = exp_bounds(mu)
    if nu <= 1:
        a, b, c = 100*nu, lo**2, hi**2
    else:
        a, b, c = 10**13 * nu**6, lo**13, hi**13
    if a <= b:
        return False
    assert a > c, 'interval is inconclusive'
    return True


@lru_cache(None)
def odd_tile(total, width, k, even):
    rate = (32-Q)/total
    return tile(rate*k/width, rate*even/width)


@lru_cache(None)
def geometry(mask):
    total = mask.bit_count()
    required, bits = 0, 0
    for j,(stride, _, x, y) in enumerate(NODES):
        a, b = (mask & x).bit_count(), (mask & y).bit_count()
        if not a+b:
            continue
        good = [odd_tile(total, 16//stride, a+b, e) for e in (a,b)]
        if not any(good):
            return None
        if not all(good):
            required |= 1 << j
            if good[1]:
                bits |= 1 << j
    q_o = (32-Q)/total
    if not tile(q_o, q_o/2):
        return None
    missing = sum(not (mask & (1 << j) or mask & (1 << (15-j))) for j in range(16))
    return required,bits,missing


def costs_and_weights(word):
    costs = [1 << k for k in range(16)]
    weights = [33]*16  # scores multiplied by 64; fair tail is 1/64
    for j in reversed(range(len(NODES))):
        stride, _, left, right = NODES[j]
        b = (word >> j) & 1
        even,odd = (right,left) if b else (left,right)
        for i in indices(even):
            if costs[i] == even:
                costs[i] = even | odd
        for i in indices(odd):
            weights[i] += 16//stride
    assert sorted(weights) == list(range(33,64,2))
    return costs, weights


def anchored_check():
    # A retained anchor leaves exactly three of twelve coordinates to be sampled.
    population, count, width = 12, 3, 5
    samples = [set(c) for c in combinations(range(population), count)]
    q = F(count, population)
    for pattern in product((0,1), repeat=width):
        i = sum(pattern)
        observed = F(sum(all((j in s)==bool(z) for j,z in enumerate(pattern))
                         for s in samples), len(samples))
        probability = F(perm(count,i)*perm(population-count,width-i),perm(population,width))
        comparison = F(population**width,perm(population,width))*q**i*(1-q)**(width-i)
        assert observed == probability and observed <= comparison
    return dict(patterns=2**width, fixed_count_samples=comb(population,count))


def run():
    assert tile(F(1), Q/32) and tile(Q,Q/2)
    assert all(tile(Q*2**k/32, Q*2**k/32) for k in (1,2,3,4))
    hist, failures, lowest, highest, witness = {},0,None,None,None
    pair_tails = {}
    for word in range(1<<15):
        costs, weights = costs_and_weights(word)
        assert sorted(m.bit_count() for m in costs)==[1]*8+[2]*4+[4]*2+[8,16]
        legal = set()
        for i in range(8):
            removed = costs[i] | costs[15-i]
            if removed.bit_count() <= 3:
                legal.add(ALL ^ removed)
        assert legal
        best = None
        for mask in legal:
            data = geometry(mask)
            if data is None or word & data[0] != data[1]:
                failures += 1
                continue
            n = mask.bit_count()
            z = sum(w for j,w in enumerate(weights) if mask & (1<<j))
            # fraction R/K: omitted common 1/2 coefficient; root direction weight missing/32.
            skew = (32-Q)/32
            exposure = ((1-skew)+skew*F(z,n))/64
            ratio = F(data[2],32)*skew/exposure
            if best is None or ratio > best[0]:
                best = ratio, mask, exposure
        assert best is not None, f'no legal support on orientation {word}'
        ratio, mask, exposure = best
        hist[mask.bit_count()] = hist.get(mask.bit_count(),0)+1
        missing = geometry(mask)[2]
        pair_tails[missing] = pair_tails.get(missing,0)+1
        if lowest is None or ratio < lowest:
            lowest, witness = ratio, dict(orientation=word,odd_supports=[2*j+1 for j in indices(mask)],
                                           exposure_before_half=str(exposure),missing_root_steps=missing)
        highest = ratio if highest is None else max(highest, ratio)
    analytic = F(1,16)*(1-Q/32) / ((Q/32 + (1-Q/32)*51)/64)
    assert lowest >= analytic
    return dict(anchored_transfer=anchored_check(),orientations=1<<15, even_rate=str(Q), failed_candidate_orientation_tests=failures,
                best_support_sizes=hist,best_holes=pair_tails,uniform_analytic_ratio=str(analytic),
                worst_best_root_ratio=str(lowest),best_orientation_root_ratio=str(highest),
                worst_certificate=witness,tile_parameters_checked=tile.cache_info().currsize)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    opts=parser.parse_args(); result=run()
    target=Path(__file__).with_name('results.json')
    saved=json.dumps(result,indent=2)+'\n'
    if opts.check:
        assert target.read_text()==saved
    else:
        target.write_text(saved)
    print(saved,end='')


if __name__=='__main__':
    main()
