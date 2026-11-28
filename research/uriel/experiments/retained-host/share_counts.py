"""Exhaustive, exact-rational control of the two cosets in Z/8Z."""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations


def profile(retained):
    """Evaluate every gamma in the source inequality, retaining its largest error."""
    size = len(retained)
    if size == 0:
        raise ValueError("The normalized discrepancy requires a nonempty set.")
    counts = [sum((t - gamma) % 2 == 0 for t in retained) for gamma in range(8)]
    weights = [Fraction(4 if gamma % 2 == 0 else 3, 7) for gamma in range(8)]
    errors = [abs(Fraction(count, size) - weight) for count, weight in zip(counts, weights)]
    return counts[:2], max(errors), sum(1 if x % 2 == 0 else -1 for x in retained)


def experiment():
    universe = set(range(8))
    omitted = {}
    accepts = set()
    boundaries = (Fraction(0), Fraction(1, 8), Fraction(1, 7))
    totals = Counter()
    for retained in combinations(range(8), 7):
        i, = universe.difference(retained)
        counts, discrepancy, char_sum = profile(retained)
        assert counts == ([3, 4] if i % 2 == 0 else [4, 3])
        assert discrepancy == (Fraction(1, 7) if i % 2 == 0 else 0)
        assert char_sum == (-1 if i % 2 == 0 else 1)
        for tolerance in boundaries:
            totals[str(tolerance)] += discrepancy <= tolerance
        if discrepancy == 0:
            accepts.add(i)
        omitted[i] = {"counts": counts, "threshold": str(discrepancy), "character_sum": char_sum}

    # A relabeling sends U \ {i} to U \ {p(i)}. Test preservation of all eight outcomes.
    permutation_counts = Counter()
    for permutation in permutations(range(8)):
        columns = [i % 2 == j % 2 for i, j in enumerate(permutation)]
        label = "preserving" if all(columns) else "interchanging" if not any(columns) else "mixed"
        agreement = sum((i in accepts) == (j in accepts) for i, j in enumerate(permutation))
        assert (agreement == 8) == (label == "preserving")
        assert (agreement == 0) == (label == "interchanging")
        permutation_counts[label] += 1
    assert totals == {"0": 4, "1/8": 4, "1/7": 8}
    assert permutation_counts == {"preserving": 576, "interchanging": 576, "mixed": 39168}
    return {"frame_order": 8, "subgroup_generator": 2, "subgroup_index": 2, "set_size": 7,
            "subsets_by_omitted_residue": omitted, "passing_subsets_by_tolerance": dict(totals),
            "permutation_classes": dict(permutation_counts)}


if __name__ == "__main__":
    print(json.dumps(experiment(), indent=2, sort_keys=True))
