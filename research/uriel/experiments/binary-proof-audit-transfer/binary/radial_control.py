"""Exact finite radial checks for a Euclidean specialization of the four-coordinate scaling law."""
from fractions import Fraction as Q
from math import isqrt, pi
import json


def two_squares(limit):
    multiplicities = [0] * (limit + 1)
    for x in range(-isqrt(limit), isqrt(limit) + 1):
        ymax = isqrt(limit - x*x)
        for y in range(-ymax, ymax + 1):
            multiplicities[x*x + y*y] += 1
    return multiplicities


def four_squares_by_coordinates(limit):
    multiplicities = [0]*(limit+1)
    multiplicities[0]=1
    squares = [(j*j, 2 if j else 1) for j in range(isqrt(limit)+1)]
    for _ in range(4):
        new=[0]*(limit+1)
        for s, m in enumerate(multiplicities):
            if m:
                for t, n in squares:
                    if t>limit-s: break
                    new[s+t] += m*n
        multiplicities=new
    return multiplicities


def check(scale):
    k2 = scale**2
    cap = 2*k2
    counts=four_squares_by_coordinates(cap)
    pairs = [(n, count) for n, count in enumerate(two_squares(cap)) if count]
    def weight(n):
        return max(0,k2-abs(2*n-3*k2))
    by_vectors=sum(n*weight(s) for s,n in enumerate(counts))
    by_pairs=sum(c*d*weight(s+t) for s,c in pairs for t,d in pairs if s+t<=cap)
    assert by_vectors==by_pairs
    lattice=Q(by_vectors,scale**6)
    length_mesh_over_pi2=Q(sum(s*weight(s) for s in range(k2,2*k2+1)),scale**6)
    expected=Q(3,4) * (1-Q(scale%2,scale**4))
    assert length_mesh_over_pi2==expected
    # The raw trace t=2s pulls dt back to 2 ds. Preserve this Jacobian explicitly.
    trace_terms = (Q(n, 2*k2) * max(0, 1 - abs(Q(n, k2)-3)) for n in range(2*k2, 4*k2+1))
    raw_trace_over_pi2 = sum(trace_terms) / k2
    assert raw_trace_over_pi2 == Q(3, 2)
    return dict(k=scale,epsilon=str(Q(1,scale)),lattice_scaled_exact=str(lattice),
                length_mesh_scaled_over_pi_squared=str(length_mesh_over_pi2),
                raw_trace_mesh_missing_jacobian_over_pi_squared=str(raw_trace_over_pi2),
                raw_trace_mesh_with_jacobian_over_pi_squared=str(raw_trace_over_pi2 / 2),
                lattice_minus_continuum_approx=float(lattice)-3*pi**2/4)


def main():
    print(json.dumps({'test':'f(s)=max(0,1-|2s-3|), s=|X|^2 in four real coordinates',
                      'limit_over_pi_squared':'3/4',
                      'scope':'The integer-lattice sample is one fixed lattice. The length-mesh sample uses only real fiber density. Neither is the published averaged adelic count.',
                      'scales':[check(k) for k in (1,2,3,4,7,8,15,16,31,32)]},indent=2))


if __name__=='__main__':main()
