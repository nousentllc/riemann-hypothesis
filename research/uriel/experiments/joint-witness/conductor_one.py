"""Compute the odd-prime index set Bchi for the primitive character of conductor one."""

import json
from itertools import count
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def reduced_forms(discriminant):
    """List primitive positive reduced forms with the usual boundary sign convention."""
    if discriminant >= 0 or discriminant % 4 not in (0, 1):
        raise ValueError("Expected a negative quadratic discriminant")
    forms = []
    for a in range(1, isqrt(-discriminant // 3) + 1):
        for b in range(-a, a + 1):
            c, remainder = divmod(b * b - discriminant, 4 * a)
            if remainder or c < a or gcd(gcd(a, b), c) != 1:
                continue
            if b < 0 and (abs(b) == a or c == a):
                continue
            forms.append([a, b, c])
    return forms


def conductor_one():
    # The group of units mod 1 is trivial. Its character has order one.
    conductor, order = 1, 1
    pk = next(p for p in count(7) if prime(p) and p % 4 == 3 and gcd(p, conductor) == 1)
    discriminant = -pk  # Here -7 is squarefree and is 1 mod 4.
    forms = reduced_forms(discriminant)
    odd_part_order = order
    while odd_part_order % 2 == 0:
        odd_part_order //= 2
    p_one = next(p for p in count(2) if prime(p) and (p - 1) % odd_part_order == 0
                 and gcd(p, 2 * conductor * pk) == 1)
    product = order * conductor * pk * len(forms) * p_one
    factors = {p for p in range(3, product + 1, 2) if prime(p) and product % p == 0}
    return dict(conductor=conductor, character_order=order, pK=pk, discriminant=discriminant,
                reduced_forms=forms, hStar=len(forms), pOne=p_one, product=product,
                Bchi=sorted(factors | {3}), status="post-registration finite specialization")


def main():
    result = conductor_one()
    if result["Bchi"] != [3, 7] or result["reduced_forms"] != [[1, 1, 2]]:
        raise ValueError(result)
    # A discriminant with a genuine +/- pair catches indiscriminate sign removal.
    if reduced_forms(-23) != [[1, 1, 6], [2, -1, 3], [2, 1, 3]]:
        raise ValueError("Reduced-form sign or boundary control failed")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
