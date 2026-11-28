"""Exact finite experiments on least-base orbit parity in cyclic dyadic groups."""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


def direct_masks(labels):
    n = len(labels)
    masks = []
    for step in range(n):
        remaining = set(range(n))
        odd = set()
        while remaining:
            t = min(remaining, key=labels.__getitem__)
            pos = 0
            while t in remaining:
                remaining.remove(t)
                if pos % 2:
                    odd.add(t)
                pos += 1
                t = (t + step) % n
        masks.append(odd)
    return masks


def tree_scores(labels):
    n = len(labels)
    cells = [list(range(n))]
    scores = [0] * n
    levels = []
    for j in range(n.bit_length() - 1):
        next_cells, odd = [], set()
        for cell in cells:
            anchor = min(cell, key=labels.__getitem__)
            left, right = [], []
            for t in cell:
                if ((t - anchor) // (1 << j)) % 2:
                    scores[t] += n >> (j + 1)
                    right.append(t)
                    odd.add(t)
                else:
                    left.append(t)
            next_cells.extend((left, right))
        cells = next_cells
        levels.append(odd)
    return scores, levels


def labelings(n):
    # SplitMix64 produces reproducible non-affine orderings, with no random module.
    def key(t):
        m = (1 << 64) - 1
        v = (t + 0x9e3779b97f4a7c15) & m
        v = ((v ^ (v >> 30)) * 0xbf58476d1ce4e5b9) & m
        v = ((v ^ (v >> 27)) * 0x94d049bb133111eb) & m
        return v ^ (v >> 31)
    return {"natural":list(range(n)), "reversed":list(reversed(range(n))),
            "scrambled":sorted(range(n), key=key)}


def occupancy_experiments():
    trials = []
    for name, labels in labelings(16).items():
        scores, _ = tree_scores(labels)
        for depth, cap in [(1,3), (2,1), (2,2), (3,1)]:
            modulus = 1 << depth
            m = 4
            greedy, counts = [], [0] * modulus
            for t in sorted(range(16), key=scores.__getitem__, reverse=True):
                if counts[t % modulus] < cap:
                    greedy.append(t)
                    counts[t % modulus] += 1
                if len(greedy) == m:
                    break
            best, multiplicity, feasible = -1, 0, 0
            for subset in combinations(range(16),m):
                if max(sum(t % modulus == c for t in subset) for c in range(modulus)) > cap:
                    continue
                feasible += 1
                weight = sum(scores[t] for t in subset)
                if weight > best:
                    best, multiplicity = weight, 1
                elif weight == best:
                    multiplicity += 1
            assert best == sum(scores[t] for t in greedy)
            trials.append({"labels":name,"size":16,"retained":4,"depth":depth,"cap":cap,
                           "feasible_sets":feasible,"number_of_maximizers":multiplicity,
                           "attainer_group_coordinates":sorted(greedy),
                           "max_mean":str(Fraction(best,16*m)),
                           "unconstrained_max_mean":str(Fraction(sum(sorted(scores)[-m:]),16*m))})
    return trials


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",type=Path)
    args = parser.parse_args()
    comparisons = cases = adjacent_cases = 0
    witness = None
    for n in [2,4,8,16,32,64,128]:
        for name, labels in labelings(n).items():
            masks = direct_masks(labels)
            scores, levels = tree_scores(labels)
            assert sorted(scores) == list(range(n))
            assert all(sum(t in odd for odd in masks) == scores[t] for t in range(n))
            for h in range(1,n):
                valuation = (h & -h).bit_length()-1
                assert levels[valuation] == masks[h]
                comparisons += n
            if name == "scrambled" and n == 16:
                bad = next(t for t in range(n) if (labels[t] % 2 == 1) != (t in masks[1]))
                witness = {"group_coordinate":bad,"numeric_label":labels[bad],"step":1,
                           "actually_odd":bad in masks[1]}
            cases += 1
    for n in (2,4,8):
        for mask in range(1 << n):
            T = {i for i in range(n) if mask & (1 << i)}
            pairs = sum(sum((t-h) % n in T for t in T) for h in range(n))
            assert pairs == len(T)**2
            adjacent_cases += 1
    results = {"cyclic_frame_checks":cases,"point_step_comparisons":comparisons,
               "adjacency_checks":adjacent_cases,"scrambled_label_negative_control":witness,
               "capped_optima":occupancy_experiments()}
    if args.check:
        assert results == json.loads(args.check.read_text()), "Stored dyadic results differ"
        print("Reproduced the dyadic parity, adjacency and sharp finite-cap experiments.")
    else:
        print(json.dumps(results,indent=2))


if __name__ == "__main__":
    main()
