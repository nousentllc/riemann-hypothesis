"""Reproduce the pinned BadOK tests. Python 3.9+, standard library only."""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial, gcd, isqrt, log
import json


@dataclass(frozen=True)
class Regime:
    e: int
    log2_x: int
    q: int
    d: int

    @property
    def n(self):
        return 2**self.e


ARMS = {
    "single_tile": Regime(15, 32, 17181966619, 17181966583),
    "density": Regime(17, 27, 274886295787, 274886296183),
    "no_tile": Regime(13, 32, 1074266443, 1074266551),
}
EPS = Fraction(1, 64)
H = 2 + 8 * EPS
K = (8 * (H + 2)) / EPS
assert K.denominator == 1
K = int(K)
R = K + 1
U = 2
ELL = (6 * R + 1) * U


def prime(n):
    if n <= 2 or n % 2 == 0:
        return n == 2
    return all(n % j for j in range(3, isqrt(n) + 1, 2))


def arithmetic(c):
    n, g = c.n, c.log2_x
    k, rank_m, rank_t = 2 * n, 2, 2 * n + 7
    q, d, modulus = c.q, c.d, 4 * n
    bound = 4 * rank_t * (k + rank_m - 1) + 1
    assert prime(q) and prime(d) and bound < min(q, d)
    assert q % 8 == 3 and d % 16 == 7 and pow(-d, (q-1)//2, q) == 1
    assert gcd(3, modulus*q*d) == 1
    assert (-d) % 3 == 2 and pow(3, (q-1)//2, q) == q-1
    assert pow(3, n, modulus) == 1 and pow(3, n//2, modulus) not in (1, modulus-1)
    a = 1
    for step in range(n):
        if a in (3, modulus-3):
            break
        a = (5 * a) % modulus
    else:
        raise AssertionError("Frobenius coordinate missing")
    assert gcd(step, n) == 1
    numerator_exp = 4 * (c.e + 1 + 26 * g)
    power, ceil_log = 1, 0
    while power < 2**numerator_exp:
        ceil_log += 1
        power *= 3
    assert 3**(ceil_log-1) < 2**numerator_exp <= 3**ceil_log
    # X'=exp(2^(g/192)). exp(11/10)>3 by its degree-five lower sum.
    # log(4)>4/3 (log(2)=2*atanh(1/3)>2/3), and 6/5<4/3.
    z = Fraction(11, 10)
    assert sum(z**i/factorial(i) for i in range(6)) > 3
    assert z**192 < 2**g < Fraction(6,5)**192
    # Order filter and ceil(1/delta)=2; 2 ramifies; 3 is the smallest inert prime.
    assert 2**g < n**256 and 0 < g < 512
    return {"n":n, "x":2**g, "k":k, "rank_m":rank_m, "rank_t":rank_t,
            "q":q, "d":d, "qd_lower_bound":bound, "QS":modulus,
            "eligible_primes":[3], "raw_step":step, "half_power":pow(3,n//2,modulus),
            "L2":2*ceil_log, "log3_argument_exp2":numerator_exp,
            "K":K, "r":R, "u":U, "tile_length":ELL, "full_tiles":n//ELL}


def histogram(items):
    counts = Counter(i % 4 for i in items)
    return [counts[j] for j in range(4)]


def marked_positions(tile_index):
    start = tile_index * ELL
    # For u=2 each even cell has exactly one even position.
    return set(range(start + 2, start + ELL, 4))


def cyclic_window_bounds(n, retained, width):
    width = min(width, n)  # image of (i+j) % n, duplicates counted once
    flags = bytearray(n)
    for i in retained:
        flags[i] = 1
    value = sum(flags[:width])
    low = high = value
    high_start = 0
    for i in range(1, n):
        value += flags[(i+width-1) % n] - flags[i-1]
        if value > high:
            high, high_start = value, i
        low = min(value, low)
    return [low, high, high_start]


def evaluate(c, a, retained):
    n = c.n
    tiles = n // ELL
    distances = []
    for j in range(tiles):
        found = {i for i in retained if j*ELL <= i < (j+1)*ELL}
        distances.append(len(found ^ marked_positions(j)))
    lo, hi, start = cyclic_window_bounds(n, retained, a["L2"])
    # (h+3)log(x)>1. M0 >= 10^(6r+1) > n. delta>1/2.
    # G'=(M0+5)*ell > n. N1 >= 6e G' delta > n.
    assert c.log2_x >= 2 and 6*R+1 >= c.e and c.log2_x < 512
    good = hi <= K and (not tiles or 0 in distances)
    size = len(retained)
    delta = 2**(-c.log2_x / 512)
    bad = 0 if good else size
    # 0 < 4 delta n / x² < 1. Cb=1 in all three arms.
    assert 4*n < a["x"]**2
    density = ((2*size)**512 * 2**c.log2_x >= n**512 and
               size**512 * 2**c.log2_x <= (2*n)**512)
    return {"size":size, "mod4":histogram(retained),
            "local_window_min":lo, "local_window_max":hi, "first_max_start":start,
            "tile_distances":distances, "tile_flags":[d==0 for d in distances],
            "cond_A":hi<=K, "cond_tiles":not tiles or 0 in distances,
            "cond_intervals":True, "good":good, "bad_point_count":bad,
            "mass_approx":round(bad*log(3)/3,8), "BadOK_Cb1":bad==0,
            "inside_density_envelope":density,
            "ordinary_budget_in_points_approx":float(format(4*n*delta/a["x"]**2,'.9g')),
            "critical_Cb_if_all_bad_approx":float(format(size*a["x"]**2/(4*n*delta),'.9g'))}


def swap(T, removed, inserted):
    assert removed in T and inserted not in T
    return (T - {removed}) | {inserted}


def study(name, c):
    a = arithmetic(c)
    n = c.n
    if name == "no_tile":
        size = K*n//a["L2"]
        T = {i for i in range(n) if (i+1)*size//n != i*size//n}
        drop, add = 4275, 3
    else:
        T = marked_positions(0)
        if name == "density":
            T |= {i for i in range(ELL,n) if i % 7 < 4}
        drop = 2
        add = next(i for i in range(ELL,n) if i%4 == drop%4 and i not in T)
    V = swap(T,drop,add)
    before, after = evaluate(c,a,T), evaluate(c,a,V)
    assert before["good"] and not after["good"]
    assert before["mod4"] == after["mod4"]
    step = a["raw_step"]
    raw = {(i*step)%n for i in T}
    assert {i for i in range(n) if i*step%n in raw} == T
    # Reverse the coordinate chart for both the labels and the generator.
    reflected = {(-v)%n for v in raw}
    assert {i for i in range(n) if (-i*step)%n in reflected} == T
    report = {"parameters":a, "swap":[drop,add], "before":before, "after":after,
              "raw_swap":[(drop*step)%n,(add*step)%n],
              "raw_mod4":histogram(raw), "coordinate_control":True}
    if name == "single_tile":
        m, capacity = len(T), n//4
        family = comb(capacity,m)
        report["fixed_mod4_family"] = {"capacity":capacity, "size":m, "passing":1,
              "total_decimal_digits":len(str(family)), "formula":f"C({capacity},{m})",
              "same_mod4_single_exchanges":m*(capacity-m)}
        assert {(i+4)%n for i in T} == V
    if name == "density":
        tail_retained = {i for i in T if i>=ELL}
        outside = set(range(n))-T
        tail_empty = {i for i in outside if i>=ELL}
        total = sum(x*y for x,y in zip(histogram(T),histogram(outside)))
        passing = sum(x*y for x,y in zip(histogram(tail_retained),histogram(tail_empty)))
        assert before["local_window_max"]+1 <= K and min(before["tile_distances"][1:])>2
        report["matched_single_exchanges"] = {"total":total, "still_passing":passing,
                "flipping":total-passing, "all_retained_mod4":histogram(T),
                "all_empty_mod4":histogram(outside), "tail_retained_mod4":histogram(tail_retained),
                "tail_empty_mod4":histogram(tail_empty)}
        lost = min(i for i in tail_retained if i%4 == add%4)
        control = evaluate(c,a,swap(T,lost,add))
        assert control["good"] and control["mod4"] == before["mod4"]
        report["tail_only_control"] = {"swap":[lost,add], "outcome":control}
    return report


def main():
    return {name:study(name,c) for name,c in ARMS.items()}


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, sort_keys=True))
