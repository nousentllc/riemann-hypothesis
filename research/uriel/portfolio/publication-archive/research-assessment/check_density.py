"""Exact density checks for the recorded q=64, base=2, j=16 scalar experiment."""
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
import subprocess
import sys


def run():
    repo = Path(__file__).resolve().parents[2] / "riemann-experiments"
    rel = "research/uriel/experiments/second"
    pin = "e674cb750ef96b2f5e7cd46586ea4edb9998715a"
    folder = repo / rel
    for name in ("arithmetic.py", "results/arithmetic.json"):
        archived = subprocess.check_output(["git", "-C", str(repo), "show", f"{pin}:{rel}/{name}"])
        if archived != (folder / name).read_bytes():
            raise ValueError(f"Input differs from the recorded experiment: {name}")
    sys.path.insert(0, str(folder))
    import arithmetic

    x, L, n, m, k, nt, n2 = [2**e for e in (1024, 16, 2177, 511, 4768, 2174, 2161)]
    rows = json.loads((folder / "results/arithmetic.json").read_text())["grid"]
    row = next(r for r in rows if (r["q"], r["base"], r["j"]) == (64, 2, 16))
    for key, value in dict(n=n, m=m, k=k, TT=nt, T2=n2).items():
        assert arithmetic.fingerprint(value) == row["fingerprints"][key]

    def density_possible(count_t, count_2):
        dt, d2 = Fraction(count_t, n), Fraction(count_2, n)
        return dt * d2**2 * (L**8 - 4*L)**2 > 32 * L**11

    def fits(count_t):
        return arithmetic.budget(x, L, n, count_t, n2, m, k)["envelope_holds"]

    d2 = Fraction(n2, n)
    A = 2*x/(m*d2) * (1 + Fraction(m*m, k))
    B = 4*m*L/d2 + Fraction(2*k*L*L, n*n)
    allowed = (isqrt(x)*(L**8 - 4*L) - 4/(x*d2))/L**5
    threshold = B/(allowed-A)
    first = -(-(n*threshold).numerator // (n*threshold).denominator)
    assert fits(first) and not fits(first-1)
    necessary = [density_possible(*counts) for counts in [(nt, n2), (nt//x, n2), (nt, n2//x)]]
    assert necessary == [True, False, False]
    endpoints = [fits(n//16384), fits(n//32768)]
    assert endpoints == [True, False]
    return {"baseline_and_two_thinned_cases_clear_necessary_bound": necessary,
            "fixed_rank_budget_at_1_over_16384_and_1_over_32768": endpoints,
            "adjacent_integer_counts_checked": True,
            "minimum_density_at_fixed_ranks_approximate": float(threshold),
            "minimum_passing_count_sha256_decimal": sha256(str(first).encode()).hexdigest()}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
