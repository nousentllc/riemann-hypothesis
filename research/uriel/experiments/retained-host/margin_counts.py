"""Post-hoc audit of the replacement coefficient and a conditional dyadic scale."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb
import json

from share_counts import profile


def replacement_audit():
    totals = Counter()
    for size in range(9):
        sets = [frozenset(u) for u in combinations(range(8), size)]
        errors = {u: size * profile(u)[1] if size else Fraction(0) for u in sets}
        for first, second in product(sets, repeat=2):
            changes = len(second - first)
            increase = errors[second] - errors[first]
            if increase > changes:
                raise ValueError("The source share discrepancy exceeded its replacement bound.")
            totals["ordered_pairs"] += 1
            if changes:
                totals["distinct_set_pairs"] += 1
                totals["equality_at_positive_distance"] += increase == changes
    expected = comb(16, 8)
    if totals["ordered_pairs"] != expected or not totals["equality_at_positive_distance"]:
        raise ValueError("The complete census or sharpness control failed.")
    return dict(totals)


def scale_substitution():
    # This checks the two size premises in the example; no numeric existence threshold is known.
    x = 2**1024
    L = 2**16  # x^eps at eps = 1/64
    density = Fraction(1, 4)  # x^(-eps/8)
    ambient_lower = x*x*L**8 // 2
    retained_lower = density * ambient_lower / 2
    room = Fraction(L-1, x) * retained_lower
    if room != 65535 * 2**1148 or retained_lower != 2**2172:
        raise ValueError("Dyadic substitution differs from the reported certified scalar bound.")
    return {"log2_scale": 1024, "epsilon": "1/64", "ambient_lower_log2": 2175,
            "retained_lower_log2": 2172, "replacement_lower": "65535 * 2^1148"}


if __name__ == "__main__":
    print(json.dumps({"finite": replacement_audit(), "conditional_example": scale_substitution()},
                     indent=2, sort_keys=True))
