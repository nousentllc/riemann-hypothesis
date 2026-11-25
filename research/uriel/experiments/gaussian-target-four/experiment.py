"""Exact residue counts with independent parity and lift controls."""
import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


def convolve(row, weights):
    modulus = len(row)
    return [sum(row[(b-a) % modulus] * w for a, w in weights.items()) for b in range(modulus)]


def histograms(modulus):
    squares = Counter(x*x % modulus for x in range(modulus))
    evens = Counter(x*x % modulus for x in range(0, modulus, 2))
    odds = squares - evens
    total = [1] + [0] * (modulus-1)
    even = total[:]
    primitive = [0] * modulus
    for dim in range(1, 7):
        still_primitive = convolve(primitive, squares)
        first_odd = convolve(even, odds)
        primitive = [a+b for a,b in zip(still_primitive, first_odd)]
        even = convolve(even, evens)
        total = convolve(total, squares)
        assert total == [a+b for a,b in zip(even, primitive)]
        assert sum(total) == modulus**dim
    return total, even, primitive


def run():
    rows = []
    target_one = []
    for r in range(11):
        m = 2**r
        total, even, primitive = histograms(m)
        target_one.append(total[1 % m])
        T, E, P = (row[4 % m] for row in (total, even, primitive))
        den = m**5
        assert 64*T == (64 if r < 4 else 63)*den
        assert 64*P == (0 if r == 0 else 62 if r == 1 else 60)*den
        if r >= 2:
            assert E == 64*target_one[r-2]
        if r <= 3:
            direct = [Counter(), Counter()]
            for x in itertools.product(range(m),repeat=6):
                direct[any(v % 2 for v in x)][sum(v*v for v in x) % m] += 1
            assert even == [direct[0][b] for b in range(m)]
            assert primitive == [direct[1][b] for b in range(m)]
        if m == 32:
            assert total[4] == total[20]
            assert {4*u*u % 32 for u in range(1, 32, 2)} == {4}
        if r >= 4:
            assert 64*total[12] == 65*den
            assert primitive[4] == primitive[12]
        rows.append(dict(depth=r,modulus=m,total=T,primitive=P,all_even=E,
                         normalized=[str(Fraction(c,den)) for c in (P,E,T)],
                         target_twelve=total[12 % m]))
    parents = {4:Counter(),12:Counter()}
    for x in itertools.product(range(8),repeat=6):
        child = sum(v*v for v in x) % 16
        if child in parents:
            parents[child]['primitive' if any(v%2 for v in x) else 'even'] += 1
    assert parents == {4:{'primitive':15360,'even':768},12:{'primitive':15360,'even':1280}}
    # A separate enumeration of the fourth odd coordinate uses actual root multiplicities.
    root_checks = {}
    for r in range(3,11):
        m = 2**r
        roots = Counter(x*x%m for x in range(1,m,2))
        assert roots == {b:4 for b in range(1,m,8)}
        root_checks[r] = len(roots)
    return {'rows':rows,'level_three_parents_by_level_four_child':parents,
            'odd_square_residues_with_four_roots':root_checks,
            'direct_vectors':sum(2**(6*r) for r in range(4))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    dest = Path(__file__).with_name('experiment.json')
    data = json.dumps(run(),indent=2)+'\n'
    if args.write:
        dest.write_text(data)
    elif dest.read_text()!=data:
        raise SystemExit('Recomputation differs from the recorded counts.')
    print('Checked 11 depths, both parity strata, sibling targets and odd-root multiplicities.')


if __name__=='__main__':
    main()
