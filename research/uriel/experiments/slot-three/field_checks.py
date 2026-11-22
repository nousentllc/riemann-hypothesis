"""Exact finite class-number certificates for Q(zeta_3) and Q(zeta_9)."""

import json
from fractions import Fraction
from math import comb, factorial, gcd, isqrt


def binary_remainder(poly, divisor):
    """Polynomial division over F_2, with coefficient i in bit i."""
    while poly.bit_length() >= divisor.bit_length():
        poly ^= divisor << (poly.bit_length() - divisor.bit_length())
    return poly


def reduced_primitive_forms(discriminant):
    """Reduced primitive positive forms, using positive b on boundary ties."""
    forms = []
    for a in range(1, isqrt((-discriminant) // 3) + 1):
        for b in range(-a, a + 1):
            c, remainder = divmod(b*b - discriminant, 4*a)
            if remainder or c < a or gcd(gcd(a, b), c) != 1:
                continue
            if (a == abs(b) or a == c) and b < 0:
                continue
            forms.append([a, b, c])
    return forms


def experiment():
    # Inscribed regular 12-gon gives pi > 3(sqrt(6)-sqrt(2)) > 31/10.
    assert 2449**2 < 6_000_000 and 1415**2 > 2_000_000
    pi_lower = Fraction(31, 10)
    assert 3 * Fraction(2449-1415, 1000) > pi_lower
    cases = {}
    for modulus, degree in ((3, 2), (9, 6)):
        # Phi_{3^n}(x) = x^(2m)+x^m+1, m=3^(n-1).
        # |N(Phi'(zeta))| = m^(2m) 3^m: Phi' = m*zeta^(m-1)*(2*zeta^m+1).
        m = modulus//3
        abs_disc = m**degree * 3**m
        sqrt_upper = isqrt(abs_disc)+1
        bound = Fraction(4, pi_lower)**(degree//2) * Fraction(factorial(degree), degree**degree) * sqrt_upper
        largest_norm = (bound.numerator-1)//bound.denominator
        poly = (1 << degree) + (1 << m) + 1
        factors = [f for f in range(2, 1 << (degree//2+1)) if binary_remainder(poly, f) == 0]
        # At 3, Phi=(x-1)^degree over F_3 and N(1-zeta)=Phi(1)=3.
        phi_mod_three = [int(i in (0, m, degree)) for i in range(degree+1)]
        power_mod_three = [comb(degree,i)*(-1)**(degree-i) % 3 for i in range(degree+1)]
        assert power_mod_three == phi_mod_three
        assert largest_norm == {3:1, 9:4}[modulus]
        assert not factors and sum(phi_mod_three)==3
        # The only rational primes <= 4 are 2 and 3. The primes above them
        # have norms 2^degree and 3 respectively, with one prime above each.
        norms = {1}
        for prime_norm in (2**degree, 3):
            for base_norm in tuple(norms):
                norm = base_norm*prime_norm
                while norm <= largest_norm:
                    norms.add(norm)
                    norm *= prime_norm
        assert norms <= {1, 3}
        cases[str(modulus)] = {
            "absolute_discriminant": abs_disc, "degree": degree,
            "strict_minkowski_upper_bound": str(bound), "largest_integer_norm_to_check": largest_norm,
            "possible_representative_norms": sorted(norms),
            "monic_F2_factors_of_degree_at_most_half": factors,
            "F3_ramified_linear_root": 1, "norm_of_one_minus_zeta": 3, "class_number": 1,
        }
    forms = {str(d): reduced_primitive_forms(d) for d in (-3,-23)}
    assert forms == {"-3":[[1,1,1]],"-23":[[1,1,6],[2,-1,3],[2,1,3]]}
    return {"field_checks":cases, "quadratic_reduced_forms":forms}


if __name__ == "__main__":
    print(json.dumps(experiment(), indent=2, sort_keys=True))
