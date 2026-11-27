"""Exact dyadic tubes by integer convolution, with direct enumeration as a control."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

def squared_histogram(modulus, parity=None):
    return Counter(x*x % modulus for x in range(modulus)
                   if parity is None or x % 2 == parity)

def convolve(dimension, modulus, parity=None):
    kernel = squared_histogram(modulus, parity)
    counts = [1] + [0] * (modulus - 1)
    for _ in range(dimension):
        counts = [sum(mult * counts[(b - sq) % modulus]
                      for sq, mult in kernel.items()) for b in range(modulus)]
    return counts

def theoretical(r, v):
    return Fraction(1) if r < 2*v + 2 else 1-Fraction(1, 4*16**v)

def run():
    tested_depths, exceptional_examples = [], []
    labels = primitive_tests = square_tests = 0
    settled = unresolved = zeros = 0
    for r in range(11):
        m = 2**r
        all_counts = convolve(6, m)
        even_counts = convolve(6, m, 0)
        assert sum(all_counts) == m**6
        if r <= 3:
            direct = Counter(sum(x*x for x in tpl) % m
                             for tpl in product(range(m), repeat=6))
            assert [direct[b] for b in range(m)] == all_counts
        for b, total in enumerate(all_counts):
            predicted = Fraction(1)
            if b:
                v = (b & -b).bit_length() - 1
                w = b >> v
                if r >= v + 2:
                    sign = 1 if w % 4 == 1 else -1
                    predicted -= Fraction(sign, 4**(v+1))
                    settled += 1
                else:
                    unresolved += 1
            else:
                zeros += 1
            assert Fraction(total, m**5) == predicted
        if r >= 2:
            for b in range(0,m,4):
                assert Fraction(all_counts[b]-even_counts[b],m**5)==Fraction(15,16)
                assert even_counts[b]==64*small_counts[b//4]
                primitive_tests += 1
        for t in range(1,257):
            v = (t & -t).bit_length()-1
            assert Fraction(all_counts[t*t % m],m**5)==theoretical(r,v)
            square_tests += 1
        labels += m
        tested_depths.append(dict(depth=r,modulus=m,
            target_unit=str(Fraction(all_counts[1%m],m**5)),
            target_4=str(Fraction(all_counts[4%m],m**5)),
            target_16=str(Fraction(all_counts[16%m],m**5)),
            target_64=str(Fraction(all_counts[64%m],m**5)),
            zero_tube=str(Fraction(all_counts[0],m**5))))
        if r <= 9:
            four = convolve(4,m)
            exceptional_examples.append(dict(depth=r,target_4_four_squares=str(Fraction(four[4%m],m**3)),
                target_16_four_squares=str(Fraction(four[16%m],m**3))))
        if r>=1:
            small_counts=prior_counts
        prior_counts=all_counts
    return dict(method="unrestricted and all-even square histograms convolved six times, arbitrary-precision integers",
                counts=dict(residues=labels,all_residue_formula_checks=labels,
                            resolved_nonzero_bins=settled,unresolved_nonzero_bins=unresolved,zero_bins=zeros,primitive_and_even_checks_at_targets_divisible_by_four=primitive_tests,
                            square_target_tests=square_tests,direct_tuple_depths=[0,1,2,3]),
                rows=tested_depths,rank_two_control=exceptional_examples)

if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
