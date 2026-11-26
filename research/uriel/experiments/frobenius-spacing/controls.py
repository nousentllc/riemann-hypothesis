"""Exact controls for the original local orbit predicates. Python 3.9+, no deps."""

from collections import Counter
from itertools import combinations
import json


def window(n, i, length):
    return {(i + j) % n for j in range(length)}


def marked(n, selected, r, u, tile):
    start = tile * (6 * r + 1) * u
    cells = [selected & set(range(start + c*u, start + (c+1)*u))
             for c in range(6*r + 1)]
    return all(not cell if c % 2 == 0 else len(cell) == 1 and min(cell) % 2 == 0
               for c, cell in enumerate(cells))


def orbit_clauses(n, selected, short_length, short_cap, r, u, lookahead,
                  long_length, long_cap):
    tiles = n // ((6*r + 1)*u)
    return {
        "short": all(len(selected & window(n, i, short_length)) <= short_cap
                     for i in range(n)),
        "tiles": all(any(marked(n, selected, r, u, (i+j) % tiles)
                         for j in range(lookahead+1)) for i in range(tiles)),
        "long": all(len(selected & window(n, i, long_length)) <= long_cap
                    for i in range(n)),
    }


def partner_offsets(n, selected, anchor, horizon, step=1):
    if anchor not in selected:
        return []
    return [offset for offset in range(1, horizon, 2)
            if (anchor + step*offset) % n in selected]


def fixed_cases():
    entries = {}
    for name, third in (("collision", 15), ("no_odd_target", 14)):
        selected = {2, 6, 10, third}
        short_counts = [len(selected & window(16, i, 8)) for i in range(16)]
        clauses = orbit_clauses(16, selected, 8, 3, 1, 2, 0, 16, 4)
        assert all(clauses.values())
        entries[name] = {
            "retained": sorted(selected),
            "clauses": clauses,
            "length_8_occupancy": short_counts,
            "offsets_horizon_8": {i: partner_offsets(16, selected, i, 8)
                                  for i in sorted(selected)},
            "offsets_horizon_16": {i: partner_offsets(16, selected, i, 16)
                                   for i in sorted(selected)},
        }
    assert entries["collision"]["offsets_horizon_8"][15] == [3, 7]
    assert entries["collision"]["offsets_horizon_16"][15] == [3, 7, 11]
    assert all(not values for values in entries["no_odd_target"]["offsets_horizon_16"].values())
    return entries


def enumeration():
    # A complete marked tile is enforced. With u=2 its three selected
    # positions are forced. Choose three more outside the 14-place tile.
    n = 32
    base = {2, 6, 10}
    summary = []
    for cap in (2, 3, 4):
        classified = Counter()
        maxima = Counter()
        pass_count = 0
        for tail in combinations(range(14, n), 3):
            selected = base | set(tail)
            result = orbit_clauses(n, selected, 8, cap, 1, 2, 1, 32, 6)
            if not all(result.values()):
                classified["rejected"] += 1
                continue
            pass_count += 1
            largest = max(len(partner_offsets(n, selected, anchor, 8))
                          for anchor in selected)
            maxima[largest] += 1
            classified["multiple" if largest >= 2 else "at_most_one"] += 1
        assert pass_count == sum(maxima.values())
        assert pass_count + classified["rejected"] == 816
        assert max(maxima, default=0) <= cap - 1
        summary.append({"short_cap": cap, "passes": pass_count,
                        "classification": dict(classified),
                        "histogram_of_maximum": dict(sorted(maxima.items()))})
    assert summary[0]["classification"].get("multiple", 0) == 0
    assert summary[1]["classification"]["multiple"] > 0
    return summary


def sharp_family():
    certificates = []
    for r in (1, 2, 7):
        for degree in (1, 2, 3, 4, 8, 16, 32):
            tile_length = (6*r + 1)*2
            length = 2*degree
            n = 1 << (tile_length + 3*length - 1).bit_length()
            anchor = tile_length + length
            marks = {2 + 4*j for j in range(3*r)}
            selected = marks | {anchor} | {anchor + e for e in range(1, length, 2)}
            tiles = n // tile_length
            clauses = orbit_clauses(n, selected, length, degree+1, r, 2,
                                    tiles-1, n, len(selected))
            assert all(clauses.values())
            edges = partner_offsets(n, selected, anchor, length)
            assert edges == list(range(1, length, 2))
            assert len(selected & window(n, anchor, length)) == degree + 1
            certificates.append({"r": r, "degree": degree, "n": n,
                                 "cap": degree+1, "tiles": tiles})
    return certificates


def incoming_control():
    selected = {2, 4, 5}
    out = {anchor: partner_offsets(16, selected, anchor, 4) for anchor in selected}
    assert out == {2: [3], 4: [1], 5: []}
    return {"retained": sorted(selected), "outgoing": out, "incoming_to_5": [2, 4]}


def main():
    report = {"fixed_cases": fixed_cases(), "n32_enumeration": enumeration(),
              "sharp_family": sharp_family(), "incoming_control": incoming_control(),
              "rank_floor": {"r_min": 6, "nWv_per_r": 660,
                             "t_min": 3954, "strict_d_floor": 94897}}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
