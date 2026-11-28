"""Post-hoc scalar obstruction for prime boxes at conductor one and epsilon=1/64."""
from fractions import Fraction as Q
from functools import lru_cache
import json


@lru_cache(maxsize=256)
def log_unit(z):
    """Directed bounds for log z, for rational 1 <= z <= 2."""
    if not 1 <= z <= 2:
        raise ValueError(z)
    t = (z-1)/(z+1)
    s = 2 * sum(t**(2*j+1)/(2*j+1) for j in range(24))
    return s, s+2*t**49/(49*(1-t*t))


def log_positive(z):
    if z < 1:
        raise ValueError("Only arguments at least one are used")
    e = z.numerator.bit_length()-z.denominator.bit_length()
    if Q(2)**e > z:
        e -= 1
    l, h = log_unit(z/Q(2)**e)
    l2, h2 = log_unit(Q(2))
    return l+e*l2, h+e*h2


def margin(k, coefficient):
    # T = 2^k, u = log T; sign of log((1+u^2)/coefficient) - u/1280.
    lo, hi = (k*v for v in log_unit(Q(2)))
    arg_lo, arg_hi = (1+lo*lo)/coefficient, (1+hi*hi)/coefficient
    return log_positive(arg_lo)[0]-hi/1280, log_positive(arg_hi)[1]-lo/1280


def certificate(k, coefficient):
    lo, hi = margin(k, coefficient)
    scale = 10**12
    return [lo.numerator*scale//lo.denominator, -((-hi.numerator*scale)//hi.denominator)]


def sign(k, coefficient):
    l, h = certificate(k, coefficient)
    if l > 0:
        return 1
    if h < 0:
        return -1
    raise ArithmeticError("Increase precision to decide the sign")


def crossing(coefficient):
    left, right = 4096, 8192
    assert sign(48, coefficient) == sign(left, coefficient) == 1
    while sign(right, coefficient) > 0:
        right *= 2
    while right-left > 1:
        mid = (left+right)//2
        if sign(mid, coefficient) > 0:
            left = mid
        else:
            right = mid
    return {"last_positive_k":left, "positive_margin_units":certificate(left,coefficient),
            "first_negative_k":right, "negative_margin_units":certificate(right,coefficient)}


def main():
    print(json.dumps({"epsilon":"1/64", "pair_scale":"2^k", "k_min":48, "margin_unit":"1e-12",
                      "lower_box_vs_cohomology":crossing(2), "upper_box_vs_cohomology":crossing(1)},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
