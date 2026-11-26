"""Exact supplemental tests for the interface comparison. Standard library only."""
from fractions import Fraction as Q
from math import gcd
import json


def prime_factors(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
        p += 1
    return factors + ([n] if n > 1 else [])


def comparison_record(q):
    phi = sum(gcd(a, q) == 1 for a in range(1, q + 1))
    terms = {str(p): str(Q(1, p-1)) for p in prime_factors(q)}
    normalized = {p: str(Q(c)/phi) for p, c in terms.items()}
    return dict(q=q, phi=phi, defect=terms, averaged_defect=normalized)


def floor_grid():
    rows = []
    for N in (2, 8, 64, 1024):
        cap = Q(N + 1, N)
        ratios = []
        for n in range(N, N + 17):
            for j in range(64):
                y = n + Q(j, 64)
                # Square the floor penalty at t = -1/2 to avoid irrational arithmetic.
                ratios.append(y/n)
                assert y/n < cap
                assert 1/y <= Q(1, N)
        assert max(ratios) == 1 + Q(63, 64*N)
        rows.append(dict(N=N, grid_max_squared=str(max(ratios)), supremum_squared=str(cap), samples=len(ratios)))
    return rows


def local_tests():
    scalar = Q(257, 128)
    tube = scalar/64
    skew = tube / Q(1, 32)
    assert tube == Q(257, 8192) and skew == Q(257, 256)
    assert 1+abs(scalar-1) > 2 and 1+abs(skew-1) <= 2
    siblings = [Q(257, 256), Q(255, 256)]
    assert sum(siblings)/2 == 1
    assert [x/sum(siblings) for x in siblings] == [Q(257,512),Q(255,512)]
    scales = []
    for k in range(1, 9):
        old = 2 + Q(2, 256**k)
        half = old/2
        assert half == 1 + Q(1,256**k)
        scales.append(dict(k=k, old=str(old), split=str(half)))
    return dict(tube=str(tube), skew=str(skew), conditional_child_probabilities=["257/512","255/512"], scales=scales)



def signed_projection():
    # Three distinct indices in each of two cosets, with two signs above every index.
    equal = unequal = mixed_equal = 0
    for mask in range(1, 1 << 12):
        counts = [(mask >> (2*i) & 3).bit_count() for i in range(6)]
        cells = [counts[:3], counts[3:]]
        n = [sum(cell) for cell in cells]
        t = [sum(m > 0 for m in cell) for cell in cells]
        if 0 in t:
            continue
        signed = [Q(x, sum(n)) for x in n]
        distinct = [Q(x, sum(t)) for x in t]
        means = [Q(x, y) for x, y in zip(n, t)]
        overall = Q(sum(n), sum(t))
        discrepancy = [p*(w/overall-1) for p, w in zip(distinct, means)]
        assert discrepancy == [s-d for s, d in zip(signed, distinct)]
        assert (signed == distinct) == (means[0] == means[1])
        if signed == distinct:
            equal += 1
            mixed_equal += int(any(len({m for m in cell if m}) > 1 for cell in cells))
        else:
            unequal += 1
    assert equal + unequal == (2**6-1)**2 and mixed_equal > 0
    return dict(nonempty_subsets=2**12-1, both_cosets=equal+unequal,
                equal_shares=equal, unequal_shares=unequal,
                equal_despite_mixed_multiplicities=mixed_equal)


def main():
    defects = [comparison_record(q) for q in (1, 2, 4, 8, 12, 18, 18480, 36960)]
    for a, b in ((1,2),(2,3),(4,5),(6,7)):
        assert defects[a]["defect"] == defects[b]["defect"]
        assert defects[a]["averaged_defect"] != defects[b]["averaged_defect"]
    assert defects[6]["phi"] == 3840 and defects[7]["phi"] == 7680
    # Midpoints, endpoints and support for a continuous hat outside every log-window.
    windows = []
    for j in range(1, 9):
        u = 4**j
        a, m, b = Q(7*u,4), 2*u, Q(9*u,4)
        def hat(v):
            return max(Q(0), 1-abs(Q(v)-m)/(b-m))
        assert Q(3*u,2) < a < m < b < 4*u
        assert [hat(v) for v in (u, Q(3*u,2),a,m,b,4*u)] == [0,0,0,1,0,0]
        windows.append(dict(U=u, center=m))
    print(json.dumps(dict(defects=defects, floor=floor_grid(), log_windows=windows, projection=signed_projection(), density=local_tests()), indent=2))


if __name__ == "__main__":
    main()
