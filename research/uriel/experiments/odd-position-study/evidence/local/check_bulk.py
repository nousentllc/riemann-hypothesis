"""Exhaustive rational audit of central even cycles with independent synthetic levels."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json


def bulk_cycle(n, mask, p, k, x=10, horizon=10000, base=100):
    """Compute the full infinite partner sum, including a certified geometric tail."""
    a0, lam = horizon * base, F(base, x)
    eta, host_n = lam / 200, 2 * n
    even = [i for i in range(0, n, 2) if mask >> i & 1]
    odd = [i for i in range(1, n, 2) if mask >> i & 1]
    top = set(even + odd)
    b = [base + (i * 3 % 6) for i in range(n)]
    a = [F(a0) * (1 + F(i, 100 * n)) for i in range(n)]
    offset = [(lam if i in top else lam / host_n) + (i % 2) * eta for i in range(n)]
    fill = [offset[i] + (b[i] if i in top else 0) for i in range(n)]
    assert p*p >= horizon and (max(b) + lam + eta) * p <= a0
    credited = {i: set() for i in even}
    used_f, used_b, rows, unmatched = F(0), F(0), F(0), 0
    for i in odd:
        d = next((d for d in range(1, n+1) if (i-d) % n in even), 0)
        cap = a[(i-d) % n] / p**d
        paired_b = min(b[i], cap) if d else F(0)
        paired_w = min(fill[i], cap) if d else F(0)
        clip = min(offset[i], max(F(0), cap - b[i])) if d else F(0)
        assert paired_w - paired_b == clip
        if d:
            credited[(i-d) % n].add(d)
        assert clip == (offset[i] if d == 1 else 0)
        unmatched += d != 1
        rows += offset[i] - k - clip
        used_f += paired_w
        used_b += paired_b
    all_partners, unused, missing = F(0), F(0), 0
    for i in even:
        e = 1
        missing += (i+1) % n not in top
        assert ((i+1) % n in top) == (1 in credited[i])
        # Include all credited exponents before the exact infinite tail.
        while e <= n or a[i] / p**e > min(fill):
            value = min(a[i] / p**e, fill[(i+e) % n])
            all_partners += value
            if e not in credited[i]:
                unused += value
            e += 2
        tail = a[i] / p**e / (1-F(1, p**2))
        all_partners += tail
        unused += tail
    total = sum((offset[i]-k for i in odd), F(0)) + used_b - all_partners
    assert all_partners - used_f == unused and total == rows - unused
    tail_cap = 2 * len(even) * F(a0, p**3) / (1-F(1, p**2))
    unused_cap = missing * (lam / host_n + eta) + tail_cap
    central = unmatched * lam
    assert 0 <= unused <= unused_cap
    low, high = central - len(odd)*k - unused_cap, central + unmatched*eta - len(odd)*k
    assert low <= total <= high and low <= max(0, total) <= central + unmatched*eta
    # This ablation removes both the lift and the unused-series corrections.
    return bool(total < central), bool(total > central), bool(total < 0), bool(unused), bool(odd and not even)


def main():
    counters = Counter()
    for n in (2, 4, 6, 8, 10):
        for mask, p, k in product(range(2**n), (101, 251, 5003, 8009), (F(0), F(1, 2), F(25, 2))):
            below, above, negative, slack, no_even = bulk_cycle(n, mask, p, k)
            counters.update(cases=1, below_unpaired_baseline=below, above_unpaired_baseline=above,
                            negative_signed_residual=negative, positive_unused=slack, odd_without_even=no_even)
    # Against treating 'predecessor exists' as an identity, on a single top row.
    b, o, k = F(100), F(10), F(3)
    partial = [dict(d=d, A=str(A), residual=str(o-k-(min(o, max(F(0), A-b)) if d else 0)))
               for d, A in ((0, 150), (1, 99), (1, 105), (1, 110), (3, 1))]
    print(json.dumps(dict(scope="synthetic rational cycles; counts include every mask, prime and lift tested",
                          counts=dict(counters), partial_row_controls=partial), indent=2))


if __name__ == '__main__':
    main()
