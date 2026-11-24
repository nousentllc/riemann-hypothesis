"""Check the integer exponents and strict endpoints of the reconstructed sufficient rank."""
from fractions import Fraction
import json


def check_case(degree, rank):
    dimension = 2 * rank**2
    haar_modulus = 2**degree
    growth_base = 2 * (haar_modulus**4)**dimension
    threshold = 2 + 8 * degree * rank**2
    sufficient_rank = 2 * threshold + 1
    if not (2**threshold > growth_base + 1 >= 2**(threshold - 1)):
        raise ValueError("Dyadic cutoff does not bracket the source inequality")
    if (Fraction(growth_base, 2**threshold), Fraction(growth_base, 2**(threshold - 1))) != (Fraction(1, 2), 1):
        raise ValueError("Unexpected majorant ratios")
    if sufficient_rank < 2 * rank or sufficient_rank != 5 + 16 * degree * rank**2:
        raise ValueError("Stable range not attained")
    if not (Fraction(sufficient_rank, 2) > threshold == Fraction(sufficient_rank - 1, 2)):
        raise ValueError("Strict endpoint failed")
    alpha = growth_base.bit_length() - 1
    real_threshold = Fraction(alpha) + Fraction(1, 4)
    refined = 2 * alpha + 1
    if growth_base != 2**alpha or Fraction(growth_base**4, 2**int(4 * real_threshold)) != Fraction(1, 2):
        raise ValueError("Real-threshold shell ratio to the fourth power must equal one half")
    if not (refined >= 2 * rank and Fraction(refined - 1, 2) == alpha < real_threshold < Fraction(refined, 2)):
        raise ValueError("Refined endpoint failed")
    return dict(real_field_degree=degree, source_rank=rank, matrix_coordinates=dimension,
                log2_growth_base=growth_base.bit_length()-1, integrability_threshold=threshold,
                sufficient_target_rank=sufficient_rank, refined_target_rank=refined,
                refined_threshold=str(real_threshold))


def main():
    cases = [check_case(degree, rank) for degree in range(1, 9) for rank in range(1, 9)]
    print(json.dumps(dict(scope="Exact scalar arithmetic, conditional on the counting inputs in the report.",
                          checked=len(cases), cases=cases), indent=2))


if __name__ == "__main__":
    main()
