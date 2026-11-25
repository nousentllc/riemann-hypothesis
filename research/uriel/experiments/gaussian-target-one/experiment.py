"""Independent exact checks on the finite residue rings. Python standard library."""
import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


def histogram(modulus, dimensions=6):
    squares = Counter((a * a) % modulus for a in range(modulus))
    row = [1] + [0] * (modulus - 1)
    for dimension in range(1, dimensions + 1):
        row = [sum(multiplicity * row[(b - square) % modulus]
                   for square, multiplicity in squares.items())
               for b in range(modulus)]
        assert sum(row) == modulus ** dimension
    return row


def run():
    rows = []
    for depth in range(11):
        modulus = 2 ** depth
        row = histogram(modulus)
        count = row[1 % modulus]
        assert 4 * count == (4 if depth < 2 else 3) * modulus ** 5
        if depth <= 3:
            direct = Counter(sum(a * a for a in vector) % modulus
                             for vector in itertools.product(range(modulus), repeat=6))
            assert all(direct[b] == n for b, n in enumerate(row))
        subgroup = list(range(1, modulus, 8))
        roots = {a*a % modulus for a in range(1,modulus,2)}
        if depth >= 3:
            assert roots == set(subgroup)
            assert all(row[b] == count for b in subgroup)
        if depth >= 2:
            assert row[3] * 4 == 5 * modulus ** 5
        rows.append(dict(depth=depth, modulus=modulus, at_one=count,
                         scalar_mass=str(Fraction(1,modulus)),
                         tube_mass=str(Fraction(count,modulus**6)),
                         density=str(Fraction(count,modulus**5)),
                         at_three=row[3 % modulus], square_classes=len(roots),
                         targets_checked=len(subgroup) if depth >= 3 else 0))
    parents = Counter()
    for vector in itertools.product(range(8),repeat=6):
        total = sum(x*x for x in vector)
        if total % 8 == 1:
            parents[total % 16] += 1
    patterns = {}
    for first in (1,3):
        parent = (first,0,0,0,0,0)
        lifts = Counter(sum((x+8*step)**2 for x,step in zip(parent,shift)) % 16
                        for shift in itertools.product((0,1), repeat=6))
        patterns[str(first)] = dict(lifts)
    assert parents == {1:12288,9:12288}
    assert patterns == {'1':{1:64},'3':{9:64}}
    return dict(levels=rows, level_three_parents_by_next_digit=dict(parents),
                first_coordinate_examples=patterns, exhaustive_vectors_through_8=sum(2**(r*6) for r in range(4)),
                unit_square_targets_checked=sum(x['targets_checked'] for x in rows),
                method='exact cyclic convolution checked against exhaustive tuples through modulus 8')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = json.dumps(run(), indent=2) + '\n'
    dest = Path(__file__).with_name('experiment.json')
    if args.write:
        dest.write_text(data)
    elif data != dest.read_text():
        raise SystemExit('The published residue checks differ from this replay.')
    print('Verified counts through modulus 1024.')


if __name__ == '__main__':
    main()
