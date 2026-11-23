"""Independent checks for the support selected by the two root representatives."""
import argparse
from fractions import Fraction
from itertools import permutations
import json
from math import gcd
from pathlib import Path
from random import Random


def support(labels, choose=min):
    n = len(labels)
    return {choose(range(j, n, 2), key=labels.__getitem__) % 8 for j in (0, 1)}


def orbit_check(labels, keep, require=True):
    n = len(labels)
    no_edges = 0
    checked = 0
    mismatches = 0
    for step in range(1, n):
        g = gcd(n, step)
        for c in range(g):
            base = min(range(c, n, g), key=labels.__getitem__)
            allowed = [((base + k * step) % 8 in keep) for k in range(n // g)]
            if not any(allowed):
                continue
            checked += 1
            a, b = sum(allowed), sum(allowed[::2])
            d = min(g, 8)
            # Expected eightfold total and even eligibility densities.
            total, even = {1: (2, 1), 2: (2, 2), 4: (4, 4), 8: (8, 4)}[d]
            mismatch = (8*a != total*len(allowed) or 8*b != even*len(allowed))
            mismatches += int(mismatch)
            if require:
                assert not mismatch
            if g == 1 and not any(v and allowed[(j + 1) % n] for j,v in enumerate(allowed)):
                no_edges += 1
    assert no_edges == n // 4
    return checked, mismatches


def cell_extrema(u):
    # A cyclic word of eight slots suffices to cover every phase and every eligible period.
    q = Fraction(21, 10*u)
    if q >= 1:
        raise ValueError("Cell width must exceed 2.1")
    empty = single = Fraction(1)
    for b in (1, 3, 5, 7):
        for h in range(1, 17):
            n, g = 32, gcd(32, h)
            for base in range(g):
                # Select a valid canonical origin for each occupied coset.
                roots = [t for t in (0,b) if t % g == base % g]
                if g < 8 and not roots:
                    continue
                if g >= 8 and base % 8 not in (0,b):
                    continue
                origin = roots[0] if g < 8 else base
                for phase in range(8):
                    slots = [j for j in range(phase, phase+u) if (origin+j*h) % 8 in (0,b)]
                    count = len(slots)
                    elig = sum(j % 2 == 0 for j in slots)
                    empty = min(empty, (1-q)**count)
                    single = min(single, elig*q*(1-q)**max(0,count-1))
    return dict(width=u, min_empty=float(empty), min_single_even=float(single),
                clears=empty >= Fraction(1,10) and single >= Fraction(1,10))


def seeded_control():
    rng = Random(20261123)
    n = 4096
    labels = list(range(n))
    rng.shuffle(labels)
    keep = support(labels, min)
    # Exact probability 21/160 on eligible sites; delta=1/16.
    chosen = {t for t in range(n) if t % 8 in keep and rng.randrange(160) < 21}
    root = min(range(n), key=labels.__getitem__)
    odd = sum((t-root) % 2 for t in chosen)
    forced = accidental = 0
    profiles = {}
    for h in range(1,n,2):
        blocked = all((c+h)%8 not in keep for c in keep)
        adjacent = sum((t+h)%n in chosen for t in chosen)
        forward_even = sum((t-root)%2 == 0 and (t+h)%n in chosen for t in chosen)
        if blocked:
            assert adjacent == forward_even == 0
            forced += 1
        else:
            accidental += adjacent == 0
        item = profiles.setdefault(str(h%8), {"steps":0,"both_directed_sum":0,"even_to_odd_sum":0})
        item["steps"] += 1
        item["both_directed_sum"] += adjacent
        item["even_to_odd_sum"] += forward_even
    assert forced == n//4 and len(chosen)>0
    return dict(n=n, eligible_classes=sorted(keep), retained=len(chosen), odd=odd,
                restriction_forced_zero_steps=forced, incidental_zero_generator_steps=accidental,
                odd_fraction=str(Fraction(odd,len(chosen))),
                normalized_forced_mass=str(Fraction(1,2)*forced/n*odd/len(chosen)),
                profiles=profiles)


def run():
    total_orbits = bad_orientations = 0
    orders = 0
    for labels in permutations(range(8)):
        keep = support(labels,min)
        total_orbits += orbit_check(labels,keep)[0]
        bad_orientations += int(orbit_check(labels,support(labels,max),False)[1] > 0)
        orders += 1
    rng = Random(731)
    extra = 0
    for n in (16,32,64,128):
        for _ in range(12):
            labels = list(range(n))
            rng.shuffle(labels)
            extra += orbit_check(labels,support(labels,min))[0]
    # For a given period class and u, exact rational comparisons determine the pass flags.
    phases = [cell_extrema(u) for u in (7,8,9,15,16,17,31,32,33,63,64,65,127,128,129,255,256)]
    assert all(v["clears"] for v in phases if v["width"] >= 64)
    return dict(label_permutations=orders, occupied_orbits=total_orbits,
                maximal_leaf_ablations_failing=bad_orientations, extra_labelings=48,
                extra_occupied_orbits=extra, cell_checks=phases, sampled=seeded_control())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    options = parser.parse_args()
    destination = Path(__file__).with_name("results.json")
    result = json.dumps(run(), indent=2) + "\n"
    if options.check:
        assert destination.read_text() == result
    else:
        destination.write_text(result)
    print("Exact orbit and cell checks complete.")


if __name__ == "__main__":
    main()
