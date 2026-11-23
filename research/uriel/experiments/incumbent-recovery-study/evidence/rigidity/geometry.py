"""Exact mod-eight geometry and finite-cell controls for the original selection rules."""

from collections import Counter
from fractions import Fraction
from itertools import permutations
import argparse
import json
from pathlib import Path


def orbits(n, h, rank):
    unseen = set(range(n))
    while unseen:
        base = min(unseen, key=rank.__getitem__)
        cycle = []
        v = base
        while v in unseen:
            unseen.remove(v)
            cycle.append(v)
            v = (v + h) % n
        assert v == base
        yield cycle


def allowed_cycle(cycle, support):
    return tuple(v % 8 in support for v in cycle)


def pair_counts(pattern):
    return tuple(sum(pattern[i] and pattern[(i+1) % len(pattern)]
                     for i in range(parity, len(pattern), 2)) for parity in (0,1))


def run():
    checks = Counter()
    patterns = set()
    expected = {"odd": (Fraction(1,4),Fraction(1,8)),
                "two": (Fraction(1,4),Fraction(1,4)),
                "four": (Fraction(1,2),Fraction(1,2)),
                "eight": (1,Fraction(1,2))}
    for order in permutations(range(8)):
        b = order[0]
        c = next(a for a in order if (a-b) % 2)
        support = {b,c}
        # A tie-free period-order lift to 16 realizes h=8 as a nontrivial step.
        rank = [2*order.index(a % 8) + (a//8) for a in range(16)]
        blocked = []
        for h in range(1,9):
            kind = "odd" if h%2 else "two" if h%4 else "four" if h%8 else "eight"
            for cycle in orbits(16,h,rank):
                mask = allowed_cycle(cycle,support)
                if not any(mask):
                    continue
                dens = (Fraction(sum(mask), len(mask)),Fraction(sum(mask[::2]),len(mask)))
                assert dens == expected[kind]
                if kind == "odd":
                    a,r = pair_counts(mask)
                    if a+r == 0:
                        blocked.append(h)
                    if a == 0 and r > 0:
                        checks["odd_direction_with_only_reverse_edges"] += 1
                patterns.add(mask)
                checks["supported_orbits"] += 1
        assert set(blocked)=={(3*(c-b))%8,(-3*(c-b))%8} and len(blocked)==2
        checks["relabellings"] += 1
    cell_results = []
    for u in (16,32,64,127,128,129,255,256,257,512):
        q = Fraction(21,10*u)
        worst_empty, worst_single = Fraction(1), Fraction(1)
        keys=set()
        for mask in patterns:
            L=len(mask)
            for start in range(L):
                eligible = sum(mask[(start+k)%L] for k in range(u))
                evens = sum(mask[(start+k)%L] and (start+k)%2==0 for k in range(u))
                keys.add((eligible,evens))
        for eligible, evens in keys:
            empty=(1-q)**eligible
            single=evens*q*(1-q)**(eligible-1)
            worst_empty=min(worst_empty,empty)
            worst_single=min(worst_single,single)
        if u>=128:
            assert min(worst_empty,worst_single)>Fraction(11,100)
        cell_results.append(dict(u=u, tested_count_pairs=len(keys),
                                 min_empty=float(worst_empty),min_even_single=float(worst_single),
                                 above_tenth=min(worst_empty,worst_single)>Fraction(1,10),
                                 above_eleven_hundredths=min(worst_empty,worst_single)>Fraction(11,100)))
    rank=list(range(16))
    broken=next(cyc for cyc in orbits(16,2,rank) if cyc[0]==1)
    broken_mask=allowed_cycle(broken,{0,3})
    assert any(broken_mask) and not any(broken_mask[::2])
    return dict(checks=dict(checks),cells=cell_results,first_passing_u_on_grid=next(
                r["u"] for r in cell_results if r["above_tenth"]),
                malformed_support=[0,3],malformed_step=2,malformed_base=1,
                malformed_cycle=broken,malformed_mask=list(map(int,broken_mask)),
                numeric_note="Comparisons use exact fractions. Decimal extrema are for display.")


def main():
    args=argparse.ArgumentParser(description=__doc__)
    args.add_argument("--check",action="store_true")
    check=args.parse_args().check
    result=run()
    serialized=json.dumps(result,indent=2)+"\n"
    target=Path(__file__).with_name("results.json")
    if check:
        assert target.read_text()==serialized
    else:
        target.write_text(serialized)
    print(result["checks"],result["cells"])


if __name__=="__main__":
    main()
