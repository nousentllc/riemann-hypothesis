"""Exact finite checks on canonical bases, heterogeneous Bernoulli means and thresholds."""
from fractions import Fraction as F
from itertools import permutations
from math import gcd, prod
import json


def indicators(n, labels):
    order = {a: i for i, a in enumerate(labels)}
    columns = []
    for h in range(1, n):
        period = n // gcd(n, h)
        assert period % 2 == 0
        cell = [-1] * n
        for a in range(n):
            if cell[a] != -1:
                continue
            orbit = [(a + i*h) % n for i in range(period)]
            base = min(orbit, key=order.__getitem__)
            for i in range(period):
                cell[(base+i*h) % n] = i % 2
        columns.append(cell)
    return columns


def arbitrary_labels():
    n = 8
    checked = 0
    for labels in permutations(range(n)):
        columns = indicators(n, labels)
        sums = [sum(column[t] for column in columns) for t in range(n)]
        assert sorted(sums) == list(range(n))
        generators = [column for h, column in enumerate(columns, 1) if gcd(n, h) == 1]
        assert all(column == generators[0] for column in generators)
        root = generators[0]
        for h, column in enumerate(columns, 1):
            if gcd(n, h) > 1:
                for b in (0, 1):
                    assert sum(2*column[a]-1 for a in range(n) if root[a] == b) == 0
        checked += 1
    return {"size": n, "labellings_checked": checked, "score_numerators": list(range(n))}


def centered_moments():
    n = 8
    columns = indicators(n, (3, 6, 1, 7, 2, 4, 0, 5))
    root = columns[0]
    delta = F(1, 2)
    probabilities = [delta if x else 3*delta/4 for x in root]
    means = [sum((2*z-1)*p for z, p in zip(col, probabilities)) for col in columns]
    weights = [2, 8, 1, 6, 4, 2, 3]
    expected = sum(w * sum(p * (1-p) for p in probabilities) for w in weights)
    observed = F(0)
    mass = F(0)
    m1 = F(0)
    raised = 0
    lowered = 0
    for mask in range(1 << n):
        selected = [t for t in range(n) if (mask >> t) & 1]
        pr = prod(p if t in selected else 1-p for t, p in enumerate(probabilities))
        signed = [sum(2*col[t]-1 for t in selected) for col in columns]
        mass += pr
        observed += pr*sum(w*(s-mu)**2 for w,s,mu in zip(weights,signed,means))
        m1 += pr*sum(w*abs(s-mu) for w,s,mu in zip(weights,signed,means))
        if selected:
            b = sum(w*s for w,s in zip(weights,signed))
            raised += int(b > 0)
            lowered += int(b < 0)
    assert observed == expected
    assert observed <= sum(weights)*delta*n
    assert m1**2 <= sum(weights)*expected
    assert mass == 1
    return {"sets_summed": 2**n, "probability_mass": str(mass), "weights": weights,
            "signed_means_odd_minus_even": [str(x) for x in means],
            "exact_weighted_variance": str(observed), "variance_cap": str(sum(weights)*delta*n),
            "weighted_first_absolute_moment": str(m1),
            "nonempty_sets_with_positive_weighted_sign": raised,
            "nonempty_sets_with_negative_weighted_sign": lowered}


def optimized(depth):
    n = 2**depth
    # m lower cells receive 3/4, n-m upper cells receive 1.
    def ratio(m):
        return (F(n, 2) - F(m*m, 8*n)) / (n-F(m, 4))
    value, m = max((ratio(m), m) for m in range(n+1))
    # Linear-fractional optimality certificate for the entire continuum of rates.
    assert all((F(2*j+1, 2*n) <= value) if j < m else
               (F(2*j+1, 2*n) >= value) for j in range(n))
    if depth <= 4:
        best = F(0)
        for mask in range(1 << n):
            a = [3+((mask >> j) & 1) for j in range(n)]
            r = F(sum((2*j+1)*v for j,v in enumerate(a)), 2*n*sum(a))
            best = max(r,best)
        assert best == value
    assert ratio(n//2) == F(15,28)
    return {"depth":depth,"low_rate_cells":m,"cells":n,"maximum":str(value),
            "maximum_decimal":round(float(value),12),"minimum":str(1-value),
            "profiles_exhaustively_checked":(1 << n) if depth <= 4 else 0}


def main():
    print(json.dumps({"arbitrary_canonical_labels":arbitrary_labels(),
                      "product_measure":centered_moments(),
                      "midpoint_profiles":[optimized(i) for i in (1,2,3,4,5,8,12)]}, indent=2))


if __name__=="__main__":
    main()
