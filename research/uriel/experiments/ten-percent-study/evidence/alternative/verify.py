"""Verify the 64-residue hand certificate for every induced labeled tree."""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
import json
from pathlib import Path


UNIFORM = F(64, 27)
DENSE, SINGLE, SPARSE = F(411, 176), F(3, 4), F(19, 8)
P_MASKS = (0x070F, 0x0331, 0x07D1, 0x0D71, 0x3101, 0x5101, 0xD107)
P_BITS = (0, 2, 5, 6, 1, 3, 4)
G_MASKS = (0x1301, 0x0D11, 0x1501, 0x5101)
WEIGHTED_MASK = 0xD101
# The local lower scores for 19, 21, 22 leaves on the dense 32-cycle.
DENSE_SCORES = {19: -195, 21: -331, 22: -362}
DENSE_SPLITS = {19: (16, 3), 21: (15, 6), 22: (16, 6)}


def members(mask, width):
    return tuple(i for i in range(width) if (mask >> i) & 1)


def bitmask(ranks):
    return sum(1 << i for i in ranks)


def swap_permutation(bits):
    """Canonical ranks to physical-prefix ranks, breadth-first input-prefix flips."""
    depth = (len(bits) + 1).bit_length() - 1
    assert len(bits) == 2 ** depth - 1
    result = []
    for rank in range(2 ** depth):
        prefix = output = 0
        for level in range(depth):
            digit = (rank >> (depth - 1 - level)) & 1
            output = 2 * output + (digit ^ bits[2**level - 1 + prefix])
            prefix = 2 * prefix + digit
        result.append(output)
    return tuple(result)


def reverse_bits(value, length):
    return int(f"{value:0{length}b}"[::-1], 2)


def chart(p, g):
    """OO coordinates in its 16-cycle; its two 8-leaf children are ± a common grid."""
    positive = tuple(2 * reverse_bits(y, 3) for y in g)
    negative = tuple((-1 - positive[p.index(j)]) % 16 for j in range(8))
    return positive + negative


def local_score(mask, width, coords=None):
    """Ten times the doubled missing-step numerator minus the doubled exposure."""
    if not mask:
        return 0
    if width == 1:
        return -1
    half = width // 2
    even, odd = mask % (1 << half), mask >> half
    if coords is None:
        missing = max(0, half - 2 * even.bit_count() * odd.bit_count())
        below_even = below_odd = None
    else:
        points = {coords[i] for i in members(mask, width)}
        missing = sum(all((t + h) % width not in points for t in points)
                      for h in range(1, width, 2))
        below_even = tuple(z // 2 for z in coords[:half])
        below_odd = tuple(z // 2 for z in coords[half:])
    return (odd.bit_count() * (20 * missing - width)
            + local_score(even, half, below_even)
            + local_score(odd, half, below_odd))


def sparse_steps(mask, p):
    n = mask.bit_count()
    pairs = sum(bool(mask & (1 << i)) and bool(mask & (1 << (8 + p[i]))) for i in range(8))
    return 16 - 2 * (n - pairs)


def score(mask, p, coords=None, weighted=False):
    count = mask.bit_count()
    odd_coefficient = local_score(mask, 16, coords) + count * (20 * sparse_steps(mask, p) - 96)
    dense_count = 22 if weighted else 26 - count
    if weighted:
        assert count == 5 and 22 * DENSE + SINGLE + 5 * SPARSE == 64
        return DENSE * DENSE_SCORES[dense_count] - 65 * SINGLE + SPARSE * odd_coefficient
    return UNIFORM * (DENSE_SCORES[dense_count] - 65 + odd_coefficient)


@cache
def exp_upper(x):
    """Rational upper enclosure through order 160 with a geometric remainder."""
    term = total = F(1)
    for k in range(1, 161):
        term *= x / k
        total += term
    assert x < 162
    return total + term * x / 161 / (1 - x / 162)


@cache
def mark(mu, nu):
    if not mu:
        return True
    if nu <= 1:
        return 100 * nu > exp_upper(2 * mu)
    return 10**13 * nu**6 > exp_upper(13 * mu)


def audit_rates(values):
    width = len(values)
    mu = sum(values) / width
    if not mu:
        return
    if width == 1:
        assert mark(mu, mu / 2), (mu, mu / 2)
        return
    half = width // 2
    nu = sum(values[:half]) / width
    assert mark(mu, nu), (mu, nu)
    audit_rates(values[:half])
    audit_rates(values[half:])


def dense_six(p):
    if p[3] >= 2:
        deleted = (3, 6, 7)
    elif p[3] == 1:
        deleted = (3, 5, 7)
    else:
        assert p[1] >= 2
        deleted = (1, 6, 7)
    chosen = tuple(i for i in range(8) if i not in deleted)
    assert any(i in deleted and 4 + p[i] in deleted for i in range(4))
    assert sum(1 + 2 * i for i in chosen) <= 33
    assert 5 * (20 * 2 - 16) - 1 - sum(1 + 2 * i for i in chosen) >= 86
    return 1 | (bitmask(chosen) << 8)


def rates_for(mask, dense_pattern, weighted):
    n = 22 if weighted else 26 - mask.bit_count()
    high, low = DENSE_SPLITS[n]
    dense_left = [1] * high + [0] * (16 - high)
    dense_right = [int(dense_pattern >> i & 1) for i in range(16)]
    assert sum(dense_right) == low
    dense_rate, single_rate, odd_rate = ((DENSE, SINGLE, SPARSE) if weighted
                                         else (UNIFORM, UNIFORM, UNIFORM))
    rates = ([dense_rate * v for v in dense_left + dense_right]
             + [single_rate] + [F(0)] * 15
             + [odd_rate * (mask >> i & 1) for i in range(16)])
    assert sum(rates) == 64
    return rates


def run():
    permutations = [(bits, swap_permutation(bits)) for bits in product((0, 1), repeat=7)]
    assert len({p for bits, p in permutations}) == 128
    reverse = tuple(range(7, -1, -1))
    six_masks = {dense_six(swap_permutation(b)) for b in product((0, 1), repeat=3)}
    three = bitmask((0, 8, 12))
    assert local_score(three, 16) == 157
    assert local_score((1 << 16) - 1, 16) == -256
    assert local_score((1 << 15) - 1, 16) == -225
    for mask in set(P_MASKS + G_MASKS + (WEIGHTED_MASK,)):
        for weighted in (False, True) if mask == WEIGHTED_MASK else (False,):
            outside = 22 if weighted else 26 - mask.bit_count()
            options = [three] if DENSE_SPLITS[outside][1] == 3 else six_masks
            for chosen in options:
                audit_rates(rates_for(mask, chosen, weighted))
    p_rows = [[] for _ in P_MASKS]
    for bits, p in permutations:
        if p == reverse:
            continue
        row = next(i for i, j in enumerate(P_BITS) if bits[j] == 0)
        mask = P_MASKS[row]
        value = score(mask, p)
        assert value > 0
        p_rows[row].append(value)
    normalized = []
    for bits, g in permutations:
        if g[0] != 0:
            continue
        sparse_chart = chart(reverse, g)
        options = [(mask, score(mask, reverse, sparse_chart)) for mask in G_MASKS]
        selected = next(((m, v, False) for m, v in options if v > 0),
                        (WEIGHTED_MASK, score(WEIGHTED_MASK, reverse, sparse_chart, True), True))
        assert selected[1] > 0
        normalized.append(dict(bits=''.join(str(bits[i]) for i in (2, 4, 5, 6)),
                               mask=f'{selected[0]:04x}', weighted=selected[2],
                               surplus=str(selected[1]), coordinates=list(sparse_chart)))
    # Check closure of the true sparse geometry under normalization (all eight unit multiples).
    by_chart = {tuple(r['coordinates']): r for r in normalized}
    lifted = Counter()
    for bits, g in permutations:
        coords = chart(reverse, g)
        unit = pow(1 + 2 * coords[0], -1, 32)
        reduced = tuple(((unit * (1 + 2 * t) % 32) - 1) // 2 for t in coords)
        row = by_chart[reduced]
        value = score(int(row['mask'], 16), reverse, coords, row['weighted'])
        assert value == F(row['surplus'])
        lifted[row['mask'], row['weighted']] += 1
    minimum = min(*(min(row) for row in p_rows), *(F(r['surplus']) for r in normalized))
    max_denominator = 64 * 127
    ratio_lower = F(1, 10) + minimum / (10 * max_denominator)
    ordinary = min(*(min(row) for row in p_rows),
                   *(F(r['surplus']) for r in normalized if not r['weighted']))
    ordinary_ratio = F(1, 10) + ordinary / (10 * max_denominator)
    dense_num, dense_den = 20, 562
    weighted_num = DENSE * dense_num + SPARSE * 96
    weighted_den = DENSE * dense_den + SINGLE * 65 + SPARSE * 583
    assert 10 * weighted_num - weighted_den == minimum == F(14, 11)
    assert ordinary_ratio > weighted_num / weighted_den
    failing = [r for r in normalized if r['weighted']]
    assert len(failing) == 1
    equal_only = max(score(mask, reverse, tuple(failing[0]['coordinates']))
                     for mask in G_MASKS)
    assert equal_only < 0
    return dict(nonreversing=[dict(mask=f'{m:04x}', cases=len(row), surplus_min=str(min(row)))
                              for m, row in zip(P_MASKS, p_rows)], reversal=normalized,
                reversal_full_counts={f'{m}/{weighted}':n for (m,weighted),n in sorted(lifted.items())},
                complete_sparse_cases=127 * 128 + sum(lifted.values()),
                mark_checks=mark.cache_info().currsize, least_surplus=str(minimum),
                denominator_upper=max_denominator, generic_ratio_lower=str(ratio_lower),
                ordinary_ratio_lower=str(ordinary_ratio),
                reversal_without_weighted_row_max_menu_surplus=str(equal_only),
                weighted_numerator_lower=str(weighted_num), weighted_denominator_upper=str(weighted_den),
                uniform_ratio_lower=str(weighted_num / weighted_den))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    out = json.dumps(run(), indent=2) + '\n'
    target = Path(__file__).with_name('results.json')
    if args.check:
        assert out == target.read_text(), 'stored certificate differs'
    else:
        target.write_text(out)
    record = json.loads(out)
    print(record['complete_sparse_cases'], record['least_surplus'], record['uniform_ratio_lower'])
