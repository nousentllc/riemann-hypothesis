"""Locate the exponent at which two disjoint aligned bands exchange order."""
from fractions import Fraction as F
from functools import lru_cache
import json

from bands import build_cells
from prime_mass import I, ZERO, ONE, S, box, sqrt_box


@lru_cache(maxsize=None)
def root_at(x, depth):
    if depth == 0:
        return box(x)
    return sqrt_box(root_at(x, depth-1))


def power_at(x, theta):
    n, denominator = theta.as_integer_ratio()
    depth = denominator.bit_length()-1
    assert denominator == 1 << depth
    value = ONE
    for j in range(depth):
        if n & (1 << j):
            value = value * root_at(x, depth-j)
    return value


def clipped(a, b, x, y, theta):
    left, right = a*x-b, a*y-b
    if max(left,right)<=0:
        return ZERO
    if min(left,right)<0:
        cut=b/a
        if left<0:
            x=cut
        else:
            y=cut
    def boundary(z):
        return power_at(z,theta).reciprocal().scale(a*z/(1-theta)+b/theta)
    return boundary(y)-boundary(x)


def interval_mass(cells, start, end, theta):
    total = ZERO
    for cell in cells:
        left,right = max(F(start), F(cell.left)),min(F(end), F(cell.right))
        if left >= right:
            continue
        lower=clipped(F(cell.a.lo,S), F(cell.b.hi,S), left, right, theta)
        upper=clipped(F(cell.a.hi,S), F(cell.b.lo,S), left, right, theta)
        total+=I(max(0,lower.lo),upper.hi)
    return total


def scan():
    cells=build_cells()
    def difference(theta):
        return interval_mass(cells,256,512,theta)-interval_mass(cells,1024,2048,theta)
    lo,hi=F(1,2),F(3,4)
    low_diff,hi_diff=difference(lo),difference(hi)
    assert low_diff.hi<0<hi_diff.lo
    for k in range(24):
        mid=(lo+hi)/2
        diff=difference(mid)
        if diff.hi<0:
            lo,low_diff=mid,diff
        elif diff.lo>0:
            hi,hi_diff=mid,diff
        else:
            raise ArithmeticError('interval comparison unresolved at '+str(mid))
    return {'steps':24,'exponent_rationals':[str(lo),str(hi)],
            'exponent_enclosure':I(box(lo).lo,box(hi).hi).pair(9),
            'first_minus_third_at_low':low_diff.pair(16),
            'first_minus_third_at_high':hi_diff.pair(16),
            'analytic_log_ratio_derivative_range':['log(2)','log(8)']}


if __name__=='__main__':
    print(json.dumps(scan(),indent=2,sort_keys=True))
