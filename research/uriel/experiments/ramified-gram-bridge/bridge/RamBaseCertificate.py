"""Regenerate and verify the packed certificate in RamBaseData.lean.

Run with no arguments to check every packed entry and the target-four controls.
Use --show to print the unpacked orbit representatives and all seven count rows.
The Lean theorem independently verifies the orbit witnesses and each recurrence.
"""

import argparse
from collections import Counter
import json
from pathlib import Path


MODULUS = 32
ORDER = MODULUS**2
HERE = Path(__file__).resolve().parent


def code(pair):
    real, uniformizer = pair
    return MODULUS * real + uniformizer


def pair(index):
    return divmod(index, MODULUS)


def multiply(left, right):
    a, b = left
    c, d = right
    return (a * c + 2 * b * d) % MODULUS, (a * d + b * c) % MODULUS


def unit_witnesses():
    units = [(a, b) for a in range(1, MODULUS, 2) for b in range(MODULUS)]
    assigned = {}
    representatives = []
    for index in range(ORDER):
        if index in assigned:
            continue
        representative_number = len(representatives)
        representatives.append(index)
        for unit in units:
            image = code(multiply(multiply(unit, unit), pair(index)))
            if image in assigned:
                continue
            a, b = unit
            scale = pow(a * a - 2 * b * b, -1, MODULUS)
            inverse = (scale * a % MODULUS, -scale * b % MODULUS)
            assert multiply(unit, inverse) == (1, 0)
            assigned[image] = (representative_number, code(unit), code(inverse))
    assert len(assigned) == ORDER and len(representatives) == 58
    return representatives, [assigned[i] for i in range(ORDER)]


def counts():
    squares = Counter(multiply(pair(i), pair(i)) for i in range(ORDER))
    rows = [Counter({(0, 0): 1})]
    for dimension in range(1, 7):
        following = Counter()
        for (a, b), multiplicity in rows[-1].items():
            for (c, d), choices in squares.items():
                following[(a + c) % MODULUS, (b + d) % MODULUS] += multiplicity * choices
        assert sum(following.values()) == ORDER**dimension
        rows.append(following)
    return rows


def declaration(name, entries, width):
    assert all(0 <= entry < 2**width for entry in entries)
    packed = sum(entry << (width * i) for i, entry in enumerate(entries))
    return f'def {name} (j : ℕ) : ℕ := (({hex(packed)} : ℕ) >>> ({width}*j)) % {2**width}'


def certificate():
    representatives, actions = unit_witnesses()
    rows = counts()
    packed = [
        declaration('repNo', [action[0] for action in actions], 6),
        declaration('rootCode', [action[1] for action in actions], 10),
        declaration('invCode', [action[2] for action in actions], 10),
        declaration('repCode', representatives, 10),
    ]
    human_rows = []
    for dimension, row in enumerate(rows):
        values = [row[pair(rep)] for rep in representatives]
        for index in range(ORDER):
            assert row[pair(index)] == values[actions[index][0]]
        packed.append(declaration(f'row{dimension}', values, max(1, max(values).bit_length())))
        human_rows.append(values)
    final = rows[-1]
    assert final[4, 0] == 257 * 2**43
    assert final[2, 0] == 17 * 2**47
    assert final[1, 0] == final[0, 0] == 2**51
    assert final[0, 1] == 0
    return packed, {'representatives': [pair(i) for i in representatives], 'counts': human_rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--show', action='store_true', help='show human-readable orbit tables')
    args = parser.parse_args()
    expected, human = certificate()
    lines = (HERE / 'RamBaseData.lean').read_text(encoding='utf-8').splitlines()
    for entry in expected:
        assert lines.count(entry) == 1, f'different certificate for {entry.split()[1]}'
    if args.show:
        print(json.dumps(human, indent=2))
    else:
        print('Verified 1,024 orbit assignments, 58 representatives, seven finite count rows, and five controls.')


if __name__ == '__main__':
    main()
