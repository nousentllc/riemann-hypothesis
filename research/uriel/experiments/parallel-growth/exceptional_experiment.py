"""Exact dyadic histograms for the exceptional-place test, using Python's standard library."""
import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


def square_counts(modulus, dimension):
    multiplicities = Counter(x*x % modulus for x in range(modulus))
    row = [1] + [0]*(modulus-1)
    for used in range(1, dimension+1):
        row = [sum(row[(b-a) % modulus]*n for a,n in multiplicities.items()) for b in range(modulus)]
        assert sum(row) == modulus**used
    return row


def run():
    rank_two = []
    rank_three = []
    for depth in range(1,12):
        modulus = 2**depth
        four = square_counts(modulus,4)
        six = square_counts(modulus,6)
        if depth <= 3:
            for row,dimension in [(four,4),(six,6)]:
                direct = Counter(sum(t*t for t in x) % modulus for x in itertools.product(range(modulus),repeat=dimension))
                assert row == [direct[b] for b in range(modulus)]
        for k in range(1,(depth-1)//2+1):
            target = 4**k
            density = Fraction(four[target % modulus],modulus**3)
            assert density == Fraction(3,target)
            assert target * density == 3
            rank_two.append(dict(depth=depth,k=k,count=four[target % modulus],density=str(density)))
        if depth >= 4:
            d3 = Fraction(six[3],modulus**5)
            d12 = Fraction(six[12],modulus**5)
            assert (d3,d12) == (Fraction(5,4),Fraction(65,64))
            rank_three.append(dict(depth=depth,at_three=str(d3),at_twelve=str(d12),
                                   ratio=str(d12/d3),raw_scaled_ratio=str(16*d12/d3)))
    # Illustrative B={2,3} over Q. Enumerating one common period is exact.
    residues = range(1,37)
    progression = [t for t in residues if t % 6 == 1]
    units = [t for t in residues if t % 2 and t % 3]
    capped = [t for t in residues if t % 4 and t % 9]
    assert set(progression) < set(units) < set(capped)
    assert (len(progression),len(units),len(capped)) == (6,12,24)
    return dict(rank_two=rank_two,rank_three=rank_three,
                illustrative_Q_residues=dict(period=36,one_mod_six=progression,
                    units_at_two_and_three=units,at_most_one_factor_each=capped),
                modulus_eight_zero_fiber_parity=dict(
                    even=sum(all(t%2==0 for t in x) and sum(t*t for t in x)%8==0
                             for x in itertools.product(range(8),repeat=4)),
                    primitive=sum(any(t%2 for t in x) and sum(t*t for t in x)%8==0
                                  for x in itertools.product(range(8),repeat=4))))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--write',action='store_true')
    args=p.parse_args()
    data=run()
    report=json.dumps(data,indent=2)+'\n'
    path=Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(report)
    elif path.read_text()!=report:
        raise ValueError('The recomputed histograms differ from the record.')
    print(f"Reproduced {len(data['rank_two'])} rank-two target-depth counts and {len(data['rank_three'])} rank-three comparisons.")


if __name__=='__main__':
    main()
