"""Finite frequency controls and an integer size certificate for the torus construction."""
import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from random import Random

import numpy as np


def walsh_counts(indicator):
    transformed = indicator.astype(np.int32, copy=True)
    width = 1
    while width < transformed.size:
        blocks = transformed.reshape(-1, 2*width)
        first = blocks[:, :width].copy()
        second = blocks[:, width:]
        blocks[:, :width] = first + second
        second[:] = first - second
        width *= 2
    return transformed


def binary_panel(d):
    n = 2**d
    m = 512
    points = np.array(Random(7021).sample(range(n), m), dtype=np.int64)
    output = {}
    for name, pts in (("spread", points), ("subgroup", np.arange(m))):
        indicator = np.zeros(n, dtype=np.int8)
        indicator[pts] = 1
        coefficients = walsh_counts(indicator)
        assert coefficients[0] == m
        assert int(np.dot(coefficients.astype(np.int64), coefficients.astype(np.int64))) == m*n
        bias = int(np.max(np.abs(coefficients[1:])))
        diff_size = len(np.unique(np.bitwise_xor.outer(pts,pts)))
        for a in (1,3,n//2+1,n-1):
            assert coefficients[a] == sum((-1)**((a & int(t)).bit_count() % 2) for t in pts)
        assert diff_size <= 1+m*(m-1)//2
        output[name] = dict(points=m, difference_count=diff_size, missing_count=n-diff_size,
                            missing_fraction=str(Fraction(n-diff_size,n)), largest_abs_character=bias,
                            min_hyperplane=(m-bias)//2, two_equation_lower_bound=str(Fraction(m-3*bias,4)))
    return dict(dimension=d,profiles=output)


def resonances():
    rows = []
    for n,radius in product((8,16,32),(1,2)):
        def near(t):
            return min(t%n,(-t)%n) <= radius
        for a,b,c,d in ((1,0,0,1),(1,1,1,-1),(2,0,0,2),(1,0,1,0)):
            det = abs(a*d-b*c)
            hits = sum(near(a*x+b*y) and near(c*x+d*y) for x,y in product(range(n),repeat=2))
            # Select a nonsingular minor; the multiplicity is at most its absolute determinant.
            bound = min(n*n,det*(2*radius+1)**2) if det else None
            if det:
                assert hits <= bound
            else:
                assert hits == n*(2*radius+1)
            rows.append(dict(grid=n,radius=radius,matrix=[a,b,c,d],det=det,hits=hits,bound=bound))
    return rows


def size_certificate(k):
    # All logs represented by integer powers of two. There is no explicit center list.
    dim = 2**k
    rank = 4096
    epsilon = Fraction(1,64)
    assert rank*epsilon/16 > 2
    log_K = 4*(k+6)
    ell = log_K+2
    log_inv_tau = 8+rank*ell
    log_M = 2*log_inv_tau+(16*(dim*ell+4)).bit_length()
    assert 2**(log_M-2*log_inv_tau) >= 16*(dim*ell+4)
    # With l=d+2 convolution factors the cube tail is <= 2d(64d)^(-2d-3).
    log_tail_upper = 1+k-(2*dim+3)*(k+6)
    assert log_tail_upper <= -8
    log_volume = 2*log_M-2*dim
    return dict(epsilon="1/64",rank=rank,dimension=dim,log2_cutoff=log_K,
                log2_centers=log_M,log2_difference_volume_bound=log_volume,
                log2_fourier_tail_bound=log_tail_upper,
                certifies_at_least_99_percent=(log_volume+6 <= -7))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    check = parser.parse_args().check
    binary = [binary_panel(d) for d in (16,19,22)]
    grids = resonances()
    certificates = [size_certificate(k) for k in range(16,24)]
    output = dict(binary=binary,grid_controls=grids,analytic_size_certificates=certificates)
    data = json.dumps(output,indent=2)+"\n"
    path = Path(__file__).with_name("frequency.json")
    if check:
        assert data == path.read_text()
    else:
        path.write_text(data)
    for row in binary:
        print(row["dimension"],row["profiles"]["spread"])
    print("resonance panels",len(grids))
    print("first certified dimension on grid",next(r for r in certificates if r["certifies_at_least_99_percent"]))


if __name__ == "__main__":
    main()
