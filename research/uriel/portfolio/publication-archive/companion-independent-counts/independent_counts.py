"""Independent exact 6-square representation counts in O/(pi^d) via 2D NTT + 3-prime CRT.

Also tests Step 3 conservation laws, child splits, and target-swap detection.
"""

from fractions import Fraction
import json
from pathlib import Path

# Three NTT-friendly primes whose product > 2^78 (max possible 6-tuple count at d=13).
PRIMES = [998244353, 1004535809, 469762049]
PRIMITIVE_ROOTS = [3, 3, 3]


def ntt_1d(a, mod, root, invert=False):
    n = len(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            a[i], a[j] = a[j], a[i]

    length = 2
    while length <= n:
        wlen = pow(root, (mod - 1) // length, mod)
        if invert:
            wlen = pow(wlen, mod - 2, mod)
        half = length >> 1
        for i in range(0, n, length):
            w = 1
            for k in range(half):
                u = a[i + k]
                v = (a[i + k + half] * w) % mod
                a[i + k] = (u + v) % mod
                a[i + k + half] = (u - v) % mod
                w = (w * wlen) % mod
        length <<= 1

    if invert:
        inv_n = pow(n, mod - 2, mod)
        for i in range(n):
            a[i] = (a[i] * inv_n) % mod


def ntt_2d(grid, rows, cols, mod, root, invert=False):
    # Transform rows
    for r in range(rows):
        row = grid[r * cols : (r + 1) * cols]
        ntt_1d(row, mod, root, invert=invert)
        grid[r * cols : (r + 1) * cols] = row
    # Transform columns
    for c in range(cols):
        col = [grid[r * cols + c] for r in range(rows)]
        ntt_1d(col, mod, root, invert=invert)
        for r in range(rows):
            grid[r * cols + c] = col[r]


def crt3(r0, r1, r2):
    p0, p1, p2 = PRIMES
    # Garner's / direct CRT for 3 primes
    inv01 = pow(p0, p1 - 2, p1)
    x1 = ((r1 - r0) % p1) * inv01 % p1
    x01 = r0 + p0 * x1
    p01 = p0 * p1
    inv01_2 = pow(p01 % p2, p2 - 2, p2)
    x2 = ((r2 - x01) % p2) * inv01_2 % p2
    return x01 + p01 * x2


def six_square_counts_table(d):
    """Return (m, n, table) where table[a * n + b] is exact # of 6-tuples summing to (a, b) mod pi^d."""
    m = 1 << ((d + 1) // 2)
    n = 1 << (d // 2)
    base = [0] * (m * n)
    for a in range(m):
        aa = a * a
        for b in range(n):
            x = (aa + 2 * b * b) % m
            y = (2 * a * b) % n
            base[x * n + y] += 1

    residues = []
    for p, g in zip(PRIMES, PRIMITIVE_ROOTS):
        arr = [v % p for v in base]
        ntt_2d(arr, m, n, p, g, invert=False)
        for idx in range(m * n):
            arr[idx] = pow(arr[idx], 6, p)
        ntt_2d(arr, m, n, p, g, invert=True)
        residues.append(arr)

    table = [crt3(residues[0][i], residues[1][i], residues[2][i]) for i in range(m * n)]
    assert sum(table) == (m * n) ** 6
    return m, n, table


def pi_power_coords(d):
    """Return (a, b) coordinates of pi^d: pi^(2r) = 2^r, pi^(2r+1) = 2^r * pi."""
    if d % 2 == 0:
        return (1 << (d // 2), 0)
    return (0, 1 << (d // 2))


def main():
    rows = []
    print("=== Step 2: Independent Exact Counts (2D NTT + CRT) ===")
    print("k  d  target       raw_count                 denom_2^(5d)         reduced_ratio")
    for k in (1, 2):
        c = 4 ** k
        for d in range(4 * k + 1, 4 * k + 6):
            m, n, table = six_square_counts_table(d)
            denom = 1 << (5 * d)

            sq_coord = (c % m, 0)
            comp_coord = (c % m, c % n)

            sq_count = table[sq_coord[0] * n + sq_coord[1]]
            comp_count = table[comp_coord[0] * n + comp_coord[1]]

            sq_ratio = Fraction(sq_count, denom)
            comp_ratio = Fraction(comp_count, denom)

            print(f"{k}  {d:<2} square       {sq_count:<25} {denom:<20} {sq_ratio}")
            print(f"{k}  {d:<2} companion    {comp_count:<25} {denom:<20} {comp_ratio}")

            rows.append({
                "k": k,
                "d": d,
                "m": m,
                "n": n,
                "denom": denom,
                "square_coord": list(sq_coord),
                "square_count": sq_count,
                "square_ratio": str(sq_ratio),
                "companion_coord": list(comp_coord),
                "companion_count": comp_count,
                "companion_ratio": str(comp_ratio),
            })

    print("\n=== Step 3: Conservation, Sibling Split & Swap Checks ===")
    for k in (1, 2):
        c = 4 ** k
        d_prev = 4 * k + 1
        m_p, n_p, tab_p = six_square_counts_table(d_prev)
        assert (c % m_p, 0) == (c % m_p, c % n_p), f"Targets not equal at predecessor depth {d_prev}"
        parent_count = tab_p[(c % m_p) * n_p + (c % n_p)]

        d_split = 4 * k + 2
        m_s, n_s, tab_s = six_square_counts_table(d_split)
        sq_child = tab_s[(c % m_s) * n_s + 0]
        comp_child = tab_s[(c % m_s) * n_s + (c % n_s)]
        assert parent_count * 64 == sq_child + comp_child, "First split conservation failed!"
        print(
            f"[k={k}] Predecessor d={d_prev}: square == companion coord {(c % m_p, c % n_p)}, "
            f"parent*64 = {parent_count * 64} == sq({sq_child}) + comp({comp_child})"
        )

        # Later split of the companion: d_split -> d_split + 1
        d_next = d_split + 1
        m_n, n_n, tab_n = six_square_counts_table(d_next)
        da, db = pi_power_coords(d_split)
        child0_coord = (c % m_n, c % n_n)
        child1_coord = ((c + da) % m_n, (c + db) % n_n)
        child0 = tab_n[child0_coord[0] * n_n + child0_coord[1]]
        child1 = tab_n[child1_coord[0] * n_n + child1_coord[1]]
        assert comp_child * 64 == child0 + child1, "Later companion split conservation failed!"
        r0 = Fraction(child0, 1 << (5 * d_next))
        r1 = Fraction(child1, 1 << (5 * d_next))
        print(
            f"[k={k}] Later companion split d={d_split}->{d_next}: "
            f"comp_parent*64 = {comp_child * 64} == child0({child0}, ratio={r0}) + child1({child1}, ratio={r1})"
        )

        # Target swap detection at d_next
        swapped_sq = tab_n[(c % m_n) * n_n + 0]
        swapped_ratio = Fraction(swapped_sq, 1 << (5 * d_next))
        expected_comp = Fraction(2) - Fraction(2, 256 ** k)
        assert swapped_ratio != expected_comp, "Swap was not detected!"
        print(
            f"[k={k}] Swap check at d={d_next}: companion={r0}, swapped_square={swapped_ratio} "
            f"(distinct: {r0} != {swapped_ratio})"
        )

    out_path = Path(__file__).parent / "independent_counts.json"
    out_path.write_text(json.dumps(rows, indent=2) + "\n")
    print(f"\nSaved exact counts to {out_path}")


if __name__ == "__main__":
    main()
