"""Independent checks of the two anchored-orbit examples in the research report.

Run python3 independent_check.py > oracle.json. Standard library, Python 3.9+.
All decisions, thresholds, and counts are certified by integers or fractions.
Decimal scores use floating point for display only.
"""

import json
from fractions import Fraction
from math import comb, exp, log


def ceil_log_base_three_of_two_power(exponent):
    """Least j with 2**exponent <= 3**j, computed by exact integer comparison."""
    lo, hi = 0, exponent
    while lo < hi:
        mid = (lo + hi) // 2
        if 3**mid >= 2**exponent:
            hi = mid
        else:
            lo = mid + 1
    return lo


def log_bracket(integer, terms=40):
    """Positive atanh series for log(integer), with a geometric tail bound."""
    z = Fraction(integer - 1, integer + 1)
    lower = 2 * sum(z**(2*j + 1) / (2*j + 1) for j in range(terms))
    upper = lower + 2*z**(2*terms + 1) / ((2*terms + 1)*(1-z*z))
    return lower, upper


def evaluate_windows(positions, order, window):
    """Evaluate all starts via a duplicated indicator and independent prefix sums."""
    if window >= order:
        return (len(positions), len(positions), 0)
    indicators = [int(i in positions) for i in range(order)]
    prefix = [0]
    for indicator in indicators + indicators:
        prefix.append(prefix[-1] + indicator)
    counts = [prefix[i+window] - prefix[i] for i in range(order)]
    return (min(counts), max(counts), counts.index(max(counts)))


def tile_distances(positions, order, tile_length):
    """Width two, absolute-even marking rule. Starts are even, both cell endpoints distinct."""
    distances = []
    for tile in range(order // tile_length):
        offset = tile * tile_length
        required = set(range(offset+2, offset+tile_length, 4))
        observed = {i for i in positions if offset <= i < offset + tile_length}
        distances.append(len(required ^ observed))
    return distances


def counts_mod_four(positions):
    counts = [0]*4
    for x in positions:
        counts[x % 4] += 1
    return counts


def product_sum(left, right):
    return sum(a*b for a, b in zip(left, right))


def solve_fixture(order_log, x_log, dense_tail):
    n = 2**order_log
    x = 2**x_log
    k = 2*n
    eps = Fraction(1, 64)
    h = 2 + 8*eps
    required = 8*(h+2)/eps
    assert required.denominator == 1
    cap = int(required)
    r = cap+1
    # delta=2**(-x_log/512) lies strictly between 1/2 and 1.
    assert 0 < x_log < 512
    u = 2
    ell = (6*r+1)*u
    head = set(range(ell))
    universe = set(range(n))
    marked_head = set(range(2, ell, 4))
    extra = {j for j in range(ell, n) if j % 7 < 4} if dense_tail else set()
    T = marked_head | extra
    v = next(i for i in range(ell,n) if i % 4 == 2 and i not in T)
    U = (T - {2}) | {v}
    assert counts_mod_four(T) == counts_mod_four(U)

    # For the model's declared prime classes, 2 is excluded and 3 is inert.
    # Prove 3 < X' < 4 by raising log(3),log(4) to the 192nd power.
    assert log_bracket(3)[1]**192 < x < log_bracket(4)[0]**192
    assert x < n**256  # x**(eps/4) < n
    # Least inert prime controls Ltwo, since log base p decreases for p>=3.
    power = 4*((order_log+1) + 26*x_log)
    l1 = ceil_log_base_three_of_two_power(power)
    l2 = 2*l1
    assert 3**(l1-1) < 2**power <= 3**l1

    # M0=ceil((h+3)*log(x)*10**(6*r+1)). Both fixtures have M0>n.
    assert (h+3)*x_log*log_bracket(2)[0]*10**6 > n and 6*r+1 >= 6
    # Hence G'>n. Since delta>1/2 and e>1, 6*e*G'*delta>n, hence N1>n.
    # The marked-tile clause reduces to existence of one mark among the complete tiles.
    assert n//ell > 0
    windows = {}
    distances = {}
    for label, points in (("initial",T), ("edited",U)):
        windows[label] = evaluate_windows(points,n,l2)
        distances[label] = tile_distances(points,n,ell)
        assert windows[label][1] <= cap
        reflected = {(-j)%n for j in points}
        # Same ambient zero, transform h to -h together with the retained set.
        assert {i for i in range(n) if (-i)%n in reflected} == points
    assert 0 in distances["initial"] and 0 not in distances["edited"]
    assert all(d>2 for d in distances["initial"][1:])
    assert 0 < Fraction(4*n,x*x) < len(T)  # normalized cutoff < score of edited set
    delta = 2**(-x_log/512)
    size = len(T)
    # Exact bounds for δ*n/2 <= m <= 2δ*n via taking 512th powers.
    density = (n**512 <= (2*size)**512 * x) and (size**512*x <= (2*n)**512)
    cert = {
        "fixture": {"group_order": n, "x": x, "rank_k":k, "epsilon":"1/64",
                    "first_inert_prime":3, "order_at_3":n, "fixed_constant_Cb":1},
        "prime_filter": [3],
        "prime_filter_upper_cutoff_decimal": exp(2**(x_log/192)),
        "K":cap, "u":u, "tile_length":ell, "cyclic_window_width":l2,
        "retained_size":size, "replacement":[2,v], "histogram_mod_4":counts_mod_four(T),
        "window_min_max_first_argmax":windows, "tile_symmetric_difference_counts":distances,
        "tile_flags":{q:[d==0 for d in ds] for q,ds in distances.items()},
        "remaining_large_window_clause_pass":True, "reflection_and_reversed_step_match":True,
        "density_condition":density,
        "normalized_bad_scores":{"initial":0,"edited":size},
        "weighted_bad_score_edited_decimal":size*log(3)/3,
        "normalized_cutoff_decimal":4*n*delta/x**2,
        "weighted_cutoff_decimal":4*n*delta/x**2*log(3)/3
    }
    if dense_tail:
        a = counts_mod_four(T)
        b = counts_mod_four(universe - T)
        c = counts_mod_four(T - head)
        d = counts_mod_four(universe - T - head)
        swaps = product_sum(a,b)
        unaffected = product_sum(c,d)
        # One removal/addition changes any window count upward by at most one.
        assert windows["initial"][1]+1 <= cap
        # A one-swap can never repair any other complete tile (distance>2).
        # The head has one unique allowed configuration, hence passes iff untouched.
        cert["matched_one_swap_census"] = {
            "all_occupied":a,"all_vacant":b,"tail_occupied":c,"tail_vacant":d,
            "all":swaps,"pass":unaffected,"fail":swaps-unaffected}
        assert (swaps,unaffected,swaps-unaffected)==(1043238003,684211212,359026791)
        assert density
    else:
        slots=n//4
        cardinality=comb(slots,size)
        assert (l2+3)//4 <= cap
        assert n//ell == 1 and len(T)==len(marked_head)
        cert["restricted_full_fiber"] = {
            "allowed_slots":slots,"retained":size,"pass":1,
            "total":str(cardinality),"fail":str(cardinality-1),
            "one_swap_flips":size*(slots-size)}
        assert not density
    return cert


def report():
    return {"case_A":solve_fixture(15,32,False),"case_B":solve_fixture(17,27,True)}


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
