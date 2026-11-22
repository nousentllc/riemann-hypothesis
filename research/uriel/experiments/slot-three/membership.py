"""Enumerate all integral center residues for Q(zeta_3) at the fixed cutoff."""
from collections import Counter
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "joint-witness"))
from center_filter import enumerate_norm, from_residue


def classify():
    prime, cutoff, modulus = 3, 64, 81
    results = {}
    histogram = Counter()
    for center in range(modulus):
        hits = enumerate_norm(prime, cutoff, center)
        if hits != from_residue(prime, cutoff, center):
            raise ValueError(f"Valuation and residue tests differ at {center}")
        if hits != ([center] if 1 <= center <= cutoff else []):
            raise ValueError(f"Unexpected finite set for residue {center}")
        results[center] = hits
        histogram[len(hits)] += 1
    weak = enumerate_norm(prime,cutoff,1,strict=False)
    if results[0] or results[1] != [1] or weak != [1,28,55]:
        raise ValueError("Distinguishing or strict-boundary control failed")
    return {
        "field": "Q(zeta_3)", "prime": prime, "cutoff": cutoff, "modulus": modulus,
        "arithmetic_basis": "RankZero.any_center under TowerClassHyp, justified mathematically by Yokoi 3(ii)",
        "strict_radius": "1/27", "decisions_compared": modulus*cutoff,
        "counts_by_set_cardinality": dict(histogram), "strict_sets_by_center_residue": results,
        "weak_comparison_for_center_1": weak,
    }


if __name__ == "__main__":
    print(json.dumps(classify(), indent=2, sort_keys=True))
