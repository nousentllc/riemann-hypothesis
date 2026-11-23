"""Exact finite controls for the bad-orbit loss study. Python standard library."""
import argparse
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def omission_control():
    strict = positive_bad_zero_omitted = assignments = 0
    pairs = set()
    for state in product(range(3), repeat=4):
        # 0 good and served, 1 bad and served, 2 bad and omitted.
        bad = sum(code != 0 for code in state)
        omitted = state.count(2)
        assert 0 <= omitted <= bad
        if bad == 0:
            assert omitted == 0
        strict += (omitted < bad)
        positive_bad_zero_omitted += (bad > 0 and omitted == 0)
        assignments += 1
        pairs.add((bad, omitted))
    assert {(2, 0), (2, 2)} <= pairs
    assert (assignments, strict, positive_bad_zero_omitted) == (81, 65, 15)
    return {"assignments": assignments, "strict_bounds": strict,
            "bad_nonempty_and_omissions_empty": positive_bad_zero_omitted,
            "omitted_counts_when_two_bad": sorted(o for b, o in pairs if b == 2)}


def exact_scales():
    rows = []
    for k in (1, 2, 3):
        x, x_epsilon = 2 ** (64 * k), 2 ** k
        bad_allowance = F(4 * x_epsilon, x)
        common_allowance = F(100 * x_epsilon ** 4, x)
        ratio = bad_allowance / common_allowance
        assert ratio == F(1, 25 * x_epsilon ** 3)
        assert 0 < bad_allowance < common_allowance
        rows.append({"log2_x": 64 * k, "tOutD_over_U": str(bad_allowance),
                     "sg": str(common_allowance), "tOutD_over_sgU": str(ratio)})
    # C_b=1. Ordinary and improved bounds absorb 16 using x^(eps/3)
    # and x^(2eps/3), respectively.
    eps = F(1, 64)
    return {"epsilon": str(eps), "K": 1, "cases": rows,
            "Cb_one_log2_absorption_thresholds":
                [int(F(4) / (eps / 3)), int(F(4) / (2 * eps / 3))]}


def prime_weight_control():
    # Two labels at each prime. Positive rational weights replace log(p)/p.
    # Multiplying a weight by p gives its corresponding log-weight surrogate.
    primes, weights, cutoff, size = (3, 7), (F(2, 3), F(3, 5)), 11, 2
    tested = zero_bad_cases = strict_bounds = 0
    for assignments in product(range(3), repeat=4):
        by_prime = (assignments[:size], assignments[size:])
        bad_mass = sum(w * sum(k != 0 for k in state)
                       for w, state in zip(weights, by_prime))
        for selected in product((0, 1), repeat=2):
            normalized_difference = sum(
                F(p, cutoff * size) * w * state.count(2)
                for p, w, state, keep in zip(primes, weights, by_prime, selected) if keep)
            assert 0 <= normalized_difference <= bad_mass / size
            if bad_mass == 0:
                assert normalized_difference == 0
                zero_bad_cases += 1
            strict_bounds += (normalized_difference < bad_mass / size)
            tested += 1
    # Same calculation with one omitted, bad label and weight one but p>X'.
    outside = F(13, 11)
    assert outside > 1
    assert (tested, zero_bad_cases, strict_bounds) == (324, 4, 320)
    return {"cases": tested, "bad_mass_zero": zero_bad_cases, "strict_bounds": strict_bounds,
            "primes": list(primes), "cutoff": cutoff, "labels": size,
            "positive_surrogate_weights": list(map(str, weights)),
            "outside_cutoff_counterexample_ratio": str(outside)}


def ledger_control():
    shares = [F(1, 20), F(1, 40), F(3, 2), F(1, 40), F(1, 40),
              F(3), F(1, 40), F(1, 30), F(1, 40)]
    all_rows, zero_rows = [], []
    for mask in product((0, 1), repeat=len(shares)):
        total = sum(c * s for c, s in zip(mask, shares))
        all_rows.append(total)
        if mask[6] == 0:
            zero_rows.append(total)
    low = sum(shares[:-1])
    low_good = low - shares[6]
    both, both_good = max(all_rows), max(zero_rows)
    assert (low, low_good, both, both_good) == (F(281, 60), F(559, 120),
                                                F(113, 24), F(281, 60))
    frontiers = []
    for name, target, rest, expected in [
            ("low", F(47, 10), low_good, F(1, 24)),
            ("combined", F(5), both_good, F(19, 60))]:
        threshold = target - rest
        excess = F(1, 1200)
        assert rest + threshold == target and threshold == expected
        assert rest + threshold + excess > target
        frontiers.append({"target": name, "permitted_orbit_cost_over_U": str(threshold),
                          "multiple_of_reserved_share": str(threshold / shares[6]),
                          "x_times_restricted_bad_mass_over_N": str(threshold / 3),
                          "boundary_violation": str(excess)})
    return {"shares": list(map(str, shares)), "corners": len(all_rows),
            "zero_seventh_share_corners": len(zero_rows), "low": str(low),
            "low_all_good": str(low_good), "combined": str(both),
            "combined_all_good": str(both_good),
            "relative_allocated_saving": str((both - both_good) / both),
            "frontiers": frontiers}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, help="compare with a stored JSON result")
    args = parser.parse_args()
    out = {"omission_control": omission_control(), "exact_scales": exact_scales(),
           "ledger_control": ledger_control(), "prime_weight_control": prime_weight_control()}
    if args.check:
        if out != json.loads(args.check.read_text()):
            raise SystemExit("Results differ from the stored comparison.")
        print("Stored comparison reproduced.")
    else:
        print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
