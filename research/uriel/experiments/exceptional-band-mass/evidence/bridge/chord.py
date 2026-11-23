"""Verify the interpolation identity and certify the area above the true chord.

The independent ramp evaluation uses a sieve. The Green representation uses
trial division. Every comparison uses directed intervals on a 160-bit grid.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "primes"))
from chi4_closed import factors, mass_affine
from prime_mass import I, S, ZERO, box, log, pow_theta, prime_powers, triangular_area


def green(x, n, a, b):
    return F((min(x, n) - a) * (b - max(x, n)), b - a)


def affine_weighted(m0, m1, a, b):
    slope = (m1 - m0) / (b - a)
    return mass_affine(slope, slope*a-m0, F(a), F(b), 2)[0]


def local_check(a, b, sieve):
    # The full curve is advanced independently; its linear term cancels exactly.
    direct = {n: log(p).scale(F(1 if n%4==1 else -1, n))
              for n,p in sieve.items() if n%2 and n <= b}
    slope = box(F(17, 23))
    intercept = ZERO
    for n, w in direct.items():
        if n <= a:
            slope, intercept = slope+w, intercept+w.scale(n)
    atoms = [(n, log(p).scale(F(1 if n%4==1 else -1, n)))
             for n,p in factors(b) if a < n < b]
    assert all(w.hi < 0 or w.lo > 0 for _,w in atoms)
    knots = [a] + [n for n,_ in atoms] + [b]
    assert sorted([n for n in direct if a < n < b]) == knots[1:-1]
    midpoints = [F(x+y, 2) for x,y in zip(knots,knots[1:])]
    points = sorted(set(knots) | set(midpoints))
    ramp = {}
    for y in points:
        ramp[y] = slope.scale(y)-intercept
        if y in direct and a < y < b:
            w = direct[y]
            slope, intercept = slope+w, intercept+w.scale(y)
    # Prefix/suffix split of the Green sum, linear on each gap.
    left = ZERO
    right = ZERO
    for n,w in atoms:
        right = right+w.scale(b-n)
    by_n = dict(atoms)
    residual = {}
    for y in points:
        if y in by_n:
            w = by_n[y]
            left, right = left+w.scale(y-a), right-w.scale(b-y)
        neg = left.scale(F(b-y,b-a)) + right.scale(F(y-a,b-a))
        curvature = ZERO-neg
        chord = ramp[a].scale(F(b-y,b-a)) + ramp[b].scale(F(y-a,b-a))
        probe = ramp[y]-chord
        assert max(curvature.lo,probe.lo) <= min(curvature.hi,probe.hi)
        if y in knots:
            if y == a or y == b:
                assert curvature.lo <= 0 <= curvature.hi
                residual[y] = ZERO  # The two ends coincide with their chord.
            else:
                residual[y] = curvature
    positive = ZERO
    weighted = ZERO
    for x,y in zip(knots,knots[1:]):
        r,s = residual[x], residual[y]
        l0,l1,h0,h1 = F(r.lo,S), F(s.lo,S), F(r.hi,S), F(s.hi,S)
        lo = box(triangular_area(l0,l1)*(y-x))
        hi = box(triangular_area(h0,h1)*(y-x))
        positive = positive+I(lo.lo,hi.hi)
        wl = affine_weighted(l0,l1,x,y)
        wh = affine_weighted(h0,h1,x,y)
        weighted = weighted+I(max(0,wl.lo),wh.hi)
    downward = ZERO
    for n,w in atoms:
        if w.hi < 0:
            downward = downward+(ZERO-w).scale(F((n-a)*(b-n),2))
    assert positive.lo <= downward.hi
    one_sign = all(w.hi<0 for _,w in atoms)
    if any(w.hi < 0 for _,w in atoms) and not one_sign:
        assert positive.hi <= downward.lo
    if one_sign:
        assert max(positive.lo,downward.lo)<=min(positive.hi,downward.hi)
    if all(w.lo>0 for _,w in atoms):
        # Outward arithmetic can retain tiny roundoff intervals at nodes.
        # Convexity supplies the exact upper zero in the one-sign case.
        assert positive.lo == 0 and positive.hi <= S // 10**24
        positive, weighted = ZERO, ZERO
    wa = pow_theta(F(a),2).scale(a).reciprocal()
    wb = pow_theta(F(b),2).scale(b).reciprocal()
    if downward.lo > 0:
        assert weighted.hi <= (wa*downward).lo
    else:
        assert weighted.hi == 0
    assert weighted.hi >= (wb*positive).lo
    return {"a":a,"b":b,"positive_jumps":sum(w.lo>0 for _,w in atoms),
            "negative_jumps":sum(w.hi<0 for _,w in atoms),"knots_and_midpoints":len(points),
            "unweighted_above_chord":positive.pair(14),"downward_curvature_cap":downward.pair(14),
            "weighted_above_chord":weighted.pair(14),"weighted_curvature_cap_upper":(wa*downward).pair(14)[1],
            "unweighted_used_share":(positive*downward.reciprocal()).pair(10) if downward.lo>0 else None}


def triangle_tests():
    checked=0
    for length in range(2,101):
        for n in range(1,length):
            height=green(n,n,0,length)
            area=height*length/2
            assert area==F(n*(length-n),2)
            assert area<=F(length**2,8)
            assert (area==F(length**2,8))==(2*n==length)
            checked+=1
    return checked


def principal_control(a,b):
    L=b-a
    exact=box(F(b*b-a*a,4))-log(F(b,a)).scale(F(a*b,2))
    lower=box(F(L**3,12*b))
    upper=box(F(L**3,12*a))
    assert lower.hi < exact.lo <= exact.hi < upper.lo
    return {"a":a,"b":b,"area":exact.pair(14),"upper":upper.pair(14)}


def main():
    sieve=prime_powers(4096)
    bands=[(486,488),(508,510),(488,490)]+[(a,2*a) for a in [256,512,1024,2048]]
    bands.extend((487-r,487+r) for r in (2,4,8,16,32))
    rows=[local_check(a,b,sieve) for a,b in bands]
    assert rows[0]["negative_jumps"]==1 and rows[0]["positive_jumps"]==0
    assert rows[1]["positive_jumps"]==1 and rows[1]["negative_jumps"]==0
    assert rows[2]["positive_jumps"]==rows[2]["negative_jumps"]==0
    print(json.dumps({"theta":"1/2","rational_triangle_tests":triangle_tests(),"smooth_principal_control":[principal_control(a,b) for a,b in ((2,3),(256,512),(486,488),(2048,2049))],"bands":rows},indent=2))


if __name__=="__main__":
    main()
