"""Compare coefficients of log(p) exactly. The unknown analytic centering is excluded."""

from collections import defaultdict
from fractions import Fraction
from math import gcd, isqrt
import json


def compare(q, y, d=7):
    # Full character lists at levels 1 and 4. Character values here are real.
    if q == 1:
        characters = [lambda n: 1]
    elif q == 4:
        characters = [lambda n: int(n % 2 == 1), lambda n: (0, 1, 0, -1)[n % 4]]
    else:
        raise ValueError("This control enumerates characters only at levels one and four")
    direct, signed, swapped = (defaultdict(Fraction) for _ in range(3))
    residues = {(r*r) % d for r in range(1, d)}
    for p in range(2, int(y) + 1):
        if any(p % i == 0 for i in range(2, isqrt(p) + 1)):
            continue
        n = p
        while n <= y:
            legendre = 0 if n % d == 0 else (1 if n % d in residues else -1)
            if (n-1) % q == 0:
                direct[p] += (1-legendre) * (Fraction(1, n)-1/y)
            for chi in characters:
                kernel = max(y/n-1, 0) / y
                signed[p] += Fraction(chi(n)*(1-legendre), len(characters)) * kernel
                swapped[p] += Fraction(chi(n)*(1+legendre), len(characters)) * kernel
            n *= p
    compact = lambda v: {str(p): str(a) for p, a in v.items() if a}
    assert compact(signed) == compact(direct)
    assert compact(swapped) != compact(direct)
    return compact(direct)


def main():
    cases = [(q, y) for q in (1, 4) for y in (Fraction(13, 2), Fraction(8), Fraction(43, 2))]
    rows = [dict(q=q, y=str(y), log_prime_coefficients=compare(q, y)) for q, y in cases]
    hand = compare(1, Fraction(4))
    assert hand == {"3": "1/6"}
    assert rows[1]["log_prime_coefficients"]["7"] == "1/56"
    phi = sum(gcd(n, 18480) == 1 for n in range(1, 18481))
    assert (phi, 2*(64*phi+3)+26) == (3840, 491552)
    print(json.dumps(dict(hand_case=hand, cases=rows, wrong_sign_rejected=len(rows)+1,
                          phi_18480=phi, real_scale_coefficient=128*phi+32), indent=2))


if __name__ == "__main__":
    main()
