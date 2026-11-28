"""Exact finite controls on a shared prime pair and a supplied pair of exception labels."""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import ceil, gcd, isqrt
from pathlib import Path


def small_prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


@lru_cache
def mersenne_prime(p):
    if not small_prime(p):
        return False
    if p == 2:
        return True
    modulus = 2**p - 1
    s = 4
    for _ in range(p - 2):
        s = (s * s - 2) % modulus
    return s == 0


def certified(d, p, a):
    """Lucas–Lehmer certifies F. The one-known-factor Pocklington criterion certifies d."""
    factor = 2**p - 1
    return (d > 2 and 1 < a < d and mersenne_prime(p)
            and (d - 1) % factor == 0 and factor * factor > d
            and pow(a, d - 1, d) == 1
            and gcd(pow(a, (d - 1) // factor, d) - 1, d) == 1)


def find_pair():
    p = 1279
    factor = 2**p - 1
    if not mersenne_prime(p):
        raise ArithmeticError("failed Lucas–Lehmer test")
    for k in range(5, 200001, 24):
        d = 2 * k * factor + 1
        if any(d % j == 0 for j in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)):
            continue
        # A failed Fermat test for base 2 proves compositeness for odd d.
        if pow(2, d - 1, d) != 1:
            continue
        for a in range(2, 101):
            if certified(d, p, a):
                return 3, d, k, a
    raise ArithmeticError("registered search exhausted")


def ln_unit(z):
    """Rigorous natural-log enclosure for 1 <= z <= 2."""
    z = Q(z)
    if not 1 <= z <= 2:
        raise ValueError("argument outside [1,2]")
    t = (z - 1) / (z + 1)
    lower = 2 * sum(t**(2*j + 1) / (2*j + 1) for j in range(12))
    return lower, lower + 2 * t**25 / (25 * (1 - t*t))


def rough_log(n):
    """Enclose ln(n); retain the mantissa for small n, otherwise use its bit length."""
    b = n.bit_length() - 1
    l2, u2 = ln_unit(2)
    ml, mu = ln_unit(Q(n, 2**b)) if n < 100 else (0, u2)
    return b*l2 + ml, b*u2 + mu


def row(q, d, qs, primality):
    # W^(eps/5) = 2^(3/20). The brackets are established by raising to 20.
    zlo, zhi = Q(1109, 1000), Q(1110, 1000)
    if not zlo**20 < 8 < zhi**20:
        raise ArithmeticError("bad enclosure of split range")
    logr = ln_unit(2)
    dlo = zlo * (48 * logr[0])**2
    dhi = zhi * (48 * logr[1])**2
    lq, uq = rough_log(q)
    ld, ud = rough_log(d)
    symbol = pow(-d % q, (q - 1) // 2, q)
    primes_below = [p for p in range(2, int(zhi) + 1) if small_prime(p)]
    clauses = {
        "q_prime": small_prime(q), "q_mod_8": q % 8 == 3,
        "q_lower": zhi / 2 < lq, "q_upper": uq <= zlo,
        "d_prime": primality, "d_mod_16": d % 16 == 7,
        "d_lower": dhi / 2 < ld, "d_upper": ud <= dlo,
        "pair_symbol_one": symbol == 1,
        "split_small": not primes_below,
        "log_product_upper": rough_log(qs*q*d)[1] <= 2*dlo,
    }
    # Make every negative interval decision used here robust to enclosure width.
    if not clauses["q_upper"] and not zhi < lq:
        raise ArithmeticError("undecided q upper bound")
    bounds = {"split_range_milli": [1109, 1110], "log_q_milli": [int(lq*1000), ceil(uq*1000)],
              "log_d_integer": [int(ld), ceil(ud)],
              "log_X2_integer": [int(dlo), ceil(dhi)],
              "log_conductor_upper_integer": ceil(rough_log(qs*q*d)[1])}
    return {"clauses": clauses, "row_all": all(clauses.values()), "bounds": bounds,
            "primes_at_or_below_split_range": primes_below, "q_divides_d_plus_one": (d+1) % q == 0}


def select(U, B, R, coords):
    """window1 in base-two log coordinates; coords are log2(exception)/Ct."""
    if len(coords) > R or R < 0 or B < 1 or U <= 0:
        raise ValueError("inadmissible selector inputs")
    current = Q(U)
    remaining = set(coords)
    erased = []
    while remaining:
        hit = sorted(v for v in remaining if current / (2*B) < v <= current)
        if not hit:
            break
        erased.append(hit[0])
        remaining.remove(hit[0])
        current /= 2*B
    return current/2, erased


def bad_at(y, B, coords):
    """Return a counterexample anywhere in [y,2y], including a boundary."""
    for a in sorted(coords):
        u = max(y, a)
        if u <= 2*y and u < B*a:
            return a, u
    return None


def exact_int(x):
    n = int(x)
    if n != x:
        raise ArithmeticError("expected integral log coordinate")
    return n


def scaled_transport(pair_log, window_log, eps):
    """Post-hoc test of winPairs, preserving the prime pair and selected field exponent."""
    alpha = 2 + 8*eps
    log_k = Q(1,10)
    log_c = alpha * log_k
    log_before = Q(2303,16)
    log_after = log_before + log_k
    e_before = ceil(alpha*log_before)
    e_after = ceil(alpha*log_after)
    log_z = log_k + window_log
    target_log = alpha*log_after

    def scaled_page(e):
        return target_log <= log_c+e <= target_log+1

    # A failed comparison of floors needs an integer gap. This control has
    # integral base-two exponents on both sides, so the floors are exact.
    bad_log_k = Q(1,2)
    bad_log_before = window_log
    bad_log_after = bad_log_k+bad_log_before
    wrong_t = exact_int(400*bad_log_after)
    available_t = exact_int(401*bad_log_before)
    return {
        "log2_k":str(log_k), "log2_c":str(log_c), "log2_x_prime":str(log_before),
        "log2_x":str(log_after), "e_x_prime":e_before, "e_x":e_after,
        "pre_pair_thresholds":max(3*log_k,400*log_k)<=pair_log,
        "final_scale_in_range":log_z<=log_after<=Q(3,2)*log_z,
        "evaluation_in_cohomology_window":window_log<=log_before<=2*window_log,
        "scaled_page_at_e_x_prime":scaled_page(e_before), "scaled_page_at_e_x":scaled_page(e_after),
        "floor_transport_by_monotonicity":400*log_after<=401*log_before,
        "bad_k_log2_half":{"cubic_window_inclusion":Q(3,2)*(window_log+bad_log_k)<=2*window_log,
                          "requested_t_log2":wrong_t, "available_t_log2":available_t,
                          "floor_transport":wrong_t<=available_t},
        "bad_k_log2_33":{"cubic_window_inclusion":Q(3,2)*(window_log+33)<=2*window_log}
    }


def run_probe():
    q, d, k, a = find_pair()
    ct, R, eta = 401, 2, Q(1, 128)
    B = exact_int(ct / eta)
    J = 2**(R + 2) * B**R
    U = 48 * J
    exc_a, exc_odd = Q(U, 2), Q(U, 4*B)
    points = {exc_a, exc_odd}
    y, removals = select(U, B, R, points)
    x = exact_int(3*y/2)
    e = ceil(Q(17, 8) * x)
    n = 2**e
    qs = 4*n
    primality = certified(d, 1279, a)
    base_row = row(q, d, qs, primality)
    changed_q = row(11, d, qs, primality)
    y_missing, _ = select(U, B, R, {exc_a})
    counter = bad_at(y_missing, B, points)
    # X^(eps/(4J))=2^(48/256)<2; the BShape bound fails if ln(q*d)>2.
    log_lower, _ = rough_log(q*d)
    if not log_lower > 2:
        raise ArithmeticError("undecided log-size control")
    # Compare with 2*X^Ct+1 by bit lengths. Never materialize X^Ct.
    if max(q.bit_length(), d.bit_length()) >= ct*U+1:
        raise ArithmeticError("undecided prime-size control")
    return {
        "pin": "40e56bab026552e089d7afcfeff08d2defb9c005",
        "coordinates": {"eps":"1/64","eta": str(eta),"Ct":ct,"B":B,"R":R,"J":J,
                        "log2_X":U,"log2_pair_scale":48,"log2_window_start":exact_int(y),"log2_x":x},
        "certificate": {"q":q,"q_bits":q.bit_length(),"d":str(d),"d_bits":d.bit_length(),"F_exponent":1279,
                        "k":k,"pocklington_base":a,"certificate_accepted":primality},
        "selector": {"two_primary_exception_log2":exact_int(ct*exc_a),
                     "odd_exception_log2":exact_int(ct*exc_odd),
                     "erased_normalized_log2":list(map(exact_int,removals)),
                     "in_range":Q(U,J)<=y and 2*y<=U,
                     "whole_union_good":bad_at(y,B,points) is None,
                     "omitted_odd_window_log2":exact_int(y_missing),
                     "violation_normalized_exception_and_point":list(map(exact_int,counter)) if counter else None},
        "selected_scale": {"e":e,"n_log2":e,"QS_log2":e+2,"t_log2":ct*x,
                           "PageN":Q(17,8)*x<=e<=Q(17,8)*x+1,
                           "PairWin":48<=x<=48*J,
                           "inside_common_window":y<=x<=2*y},
        "post_hoc_winPairs_transport":scaled_transport(48, y, Q(1,64)),
        "original_q":base_row,"mutant_q11":changed_q,
        "prime_pair_conductor_one":all([small_prime(q),primality,q%8==3,d%16==7,gcd(q*d,1)==1]),
        "mutant_prime_pair_conductor_one":small_prime(11) and 11%8==3 and primality and d%16==7,
        "cohomological_prerequisites":{"log_qd_lower_integer":int(log_lower),
              "log_qd_bound_rhs_power_of_two":"3/16","log_size_pass":False,
              "q_gt_2XpowCt_plus_1":False,"d_gt_2XpowCt_plus_1":False,
              "large_prime_cutoff_log2_lower":ct*U+1,"eventual_X0":"unknown"},
        "fixture_inputs":["Ck","R0","odd budget","exception labels","QS = 4n","conductor 1"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    output = run_probe()
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
