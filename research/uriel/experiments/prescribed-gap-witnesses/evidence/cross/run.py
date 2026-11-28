"""Retain a fixed, proved prime row through one strict ternary precision boundary."""
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PAIR = HERE.parent / "pairs"
sys.path.insert(0, str(PAIR))
from prime_rows import Interval, check_certificate, elementary, exact, show, strict


def positive_product(a, b):
    assert a.lo >= 0 and b.lo >= 0
    return Interval(a.lo * b.lo, a.hi * b.hi)


def positive_ratio(a, b):
    assert a.lo >= 0 and b.lo > 0
    return Interval(a.lo / b.hi, a.hi / b.lo)


def source_row(u, q, d):
    z = u.scale(Fraction(1, 360)).exp()
    h = positive_product(positive_product(u, u), z)
    log_q, log_d = (elementary("ln", exact(p)) for p in (q, d))
    # The archived certificate establishes primality of d; q is the prime 3.
    assert q == 3 and q % 8 == 3 and d % 16 == 7 and (d + 1) % q == 0
    assert 1 <= z.lo <= z.hi < 2  # no odd prime at or below z
    assert strict(z.scale(Fraction(1, 2)), log_q) and strict(log_q, z)
    assert strict(h.scale(Fraction(1, 2)), log_d) and strict(log_d, h)
    assert strict(u, exact(72)) and strict(exact(76), u.scale(4))
    return z, h


def run():
    evidence = (PAIR / "results.json").read_bytes()
    prior = json.loads(evidence)
    assert prior["eps"] == "1/72" and prior["J"] == 4
    assert prior["fixed_target_log_coordinates"] == [72, 76]
    d = check_certificate(prior["certificate"])
    assert d.bit_length() == 1400
    q = prior["q"]
    k = 100
    log3 = elementary("ln", exact(3))
    frequency = 4 * 401
    nearest_ratio = positive_ratio(exact(frequency * 36), log3)
    m = (nearest_ratio + exact(Fraction(1, 2))).floor()
    assert abs(nearest_ratio.lo - m) < Fraction(1, 2) and abs(nearest_ratio.hi - m) < Fraction(1, 2)
    pivot = log3.scale(Fraction(m, frequency))
    delta = Fraction(1, 10**12)
    before, after = pivot - exact(delta), pivot + exact(delta)
    rows = []
    bands = []
    for u, expected in ((before, m), (after, m + 1)):
        z, h = source_row(u, q, d)
        bands.append((z, h))
        # For integer powers P of three, P<=floor(exp(v)) iff P<=exp(v).
        # The closed lower and strictly open upper powers can therefore be
        # certified exactly in log scale, without materializing floor(exp(v)).
        v = u.scale(frequency)
        log3_cut = positive_ratio(v, log3)
        depth = log3_cut.floor()
        assert depth + 1 == expected
        assert strict(log3.scale(depth), v) and strict(v, log3.scale(depth + 1))
        rows.append(dict(logY=show(u, 17), z=show(z, 13), H=show(h, 13),
                         real_log3_outer_power=show(log3_cut, 13), strict_precision=depth + 1,
                         win_pair=True, target_in_ambient=True, odd_small_primes=[]))
    # s'=100+3^m agrees modulo 3^m with 100. Its later canonical
    # representative is s' itself, since 100<2*3^m.
    log_k = elementary("ln", exact(k))
    log_k1 = elementary("ln", exact(k + 1))
    log_power = log3.scale(m)
    assert strict(log_k1, exact(401 * 72)) and strict(exact(Fraction(76, 144)), log_k)
    assert strict(exact(401 * 76), log_power) and strict(log_k, log_power)
    # exp(v)-3^m = 3^m*(exp(frequency*delta)-1) > 3^m*frequency*delta > 100.
    log_threshold = elementary("ln", exact(Fraction(k, 1) / (frequency * delta)))
    assert strict(log_threshold, log_power)
    early, late = bands
    d_guard = strict(late[1].scale(Fraction(1, 2)).exp(),
                     exact(early[1].scale(Fraction(1, 2)).exp().floor() + 1))
    assert not d_guard
    return dict(target_log=[72, 76], eps="1/72", J=4, Ct=401, positive_allowance_ceiling="1/144",
                prior_receipt_sha256=sha256(evidence).hexdigest(), q=q, d_bits=d.bit_length(),
                source_congruences={"q_mod_8": q % 8, "d_mod_16": d % 16, "q_divides_d_plus_1": (d + 1) % q == 0},
                nearest_integer=m, pivot_logY=show(pivot, 17), offsets=["-1/1000000000000", "1/1000000000000"],
                queries=rows, earlier_input_only_d_guard=d_guard,
                old_modulus=f"3^{m}", new_modulus=f"3^{m+1}",
                active_cutoff_at_left_exceeds_100=True, allowance_at_right=show(exact(Fraction(76, 144)).exp(), 12),
                persistent={"center":"100", "left_record":["100"], "right_record":["100"], "passes_everywhere":[False,False]},
                clearing={"center":f"100+3^{m}", "left_record":["100"], "right_record":[f"100+3^{m}"],
                          "new_label_below_later_outer_cutoff_or_equal":True, "new_label_above_all_active_cutoffs":True,
                          "passes_everywhere":[False,True]},
                scope="Same genuine finite WinPair, two legal rank-one slot-3 center choices and two distinct precisions. q=3 is ineligible for full host assembly. PairGood and the actual global K are not supplied by this finite row.")


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
