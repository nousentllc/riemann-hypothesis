"""Produce a literal modulo-64 certificate from the residues in increasing label order."""
import argparse
from fractions import Fraction as F
from functools import cache
import json
from pathlib import Path

PRIMARY = (
    (0, (0, 1, 2, 3, 8, 9, 10)), (2, (0, 4, 5, 8, 9)),
    (5, (0, 4, 6, 7, 8, 9, 10)), (6, (0, 4, 5, 6, 8, 10, 11)),
    (1, (0, 8, 12, 13)), (3, (0, 8, 12, 14)), (4, (0, 1, 2, 8, 12, 14, 15)),
)
REVERSED = ((0, 8, 9, 12), (0, 4, 8, 10, 11), (0, 8, 10, 12), (0, 8, 12, 14))
HARD = (0, 8, 12, 14, 15)
GUARANTEE = F(12087, 120814)


def lexicographic_tree(ranking, sites, stride):
    """Return canonical leaf ranks, descending through the preferred child first."""
    if len(sites) == 1:
        return list(sites)
    center = min(sites, key=ranking.__getitem__)
    even = [i for i in sites if (i-center) % (2*stride) == 0]
    odd = [i for i in sites if (i-center) % (2*stride) != 0]
    return lexicographic_tree(ranking, even, stride*2) + lexicographic_tree(ranking, odd, stride*2)


def six(block):
    """Use one minimum plus five surviving odd leaves in a sixteen-leaf node."""
    center = block[0]
    ranks = block[8:]
    pairing = [ranks[4:].index((2*center-t) % 64) for t in ranks[:4]]
    if pairing[3] >= 2:
        delete = {3, 6, 7}
    elif pairing[3] == 1:
        delete = {3, 5, 7}
    else:
        assert pairing[1] >= 2
        delete = {1, 6, 7}
    return [center] + [t for j,t in enumerate(ranks) if j not in delete]


def reservoir(block, count):
    if count == 19:
        return block[:16] + [block[i] for i in (16, 24, 28)]
    if count in (21, 22):
        return block[:count-6] + six(block[16:])
    raise ValueError("No reservoir of the requested size")


@cache
def tile(total, even):
    """Strict rational upper bound on exp(total), including the positive remainder."""
    if total == 0:
        return True
    term = low = F(1)
    for k in range(1, 33):
        term *= total / k
        low += term
    upper = low + term*total/33 / (1-total/34)
    if even <= 1:
        return upper**2 < 100*even
    return upper**13 < 10**13 * even**6


def ledger(order, rates):
    rows = []
    for w in (64, 32, 16, 8, 4, 2):
        stride = 64//w
        for i in range(0, 64, w):
            node = order[i:i+w]
            active = {t for t in node if rates.get(t, 0) > 0}
            if not active:
                continue
            mass = sum(rates[t] for t in active)
            even_mass = sum(rates.get(t, 0) for t in node[:w//2])
            assert tile(mass/w, even_mass/w)
            missing = [h for h in range(1,w,2)
                       if all((t+stride*h) % 64 not in active for t in active)]
            odd = mass-even_mass
            rows.append(dict(width=w, coset=node[0] % stride, missing=missing,
                             odd_mass=str(odd), numerator=str(2*len(missing)*odd),
                             denominator=str(w*odd)))
    for a in set(rates.values()):
        assert tile(a,a/2)
    numerator = sum(F(r["numerator"]) for r in rows)
    denominator = sum(rates.values()) + sum(F(r["denominator"]) for r in rows)
    return rows, numerator, denominator


def switches(p):
    word = 0
    for level in range(3):
        w = 8 >> level
        for j in range(1 << level):
            bit = (p[j*w] % w) // (w//2)
            word |= bit << ((1 << level)-1+j)
    return word


def certificate(labels):
    if sorted(labels) != list(range(64)):
        raise ValueError("Supply the 64 residues once each in increasing order of numeric label.")
    order = lexicographic_tree({t:i for i,t in enumerate(labels)}, list(range(64)), 1)
    center = order[32]
    tips = order[48:]
    pairing = [tips[8:].index((2*center-t) % 64) for t in tips[:8]]
    word = switches(pairing)
    if word == 127:
        unit = pow(((tips[0]-center) % 64)//2, -1, 32)
        coords = [((((t-center) % 64)//2 * unit) % 32 - 1)//2 for t in tips]
        assert coords[0] == 0 and all(i % 2 == 0 for i in coords[:8])
        chart_word = switches([reverse_bits(i//2,3) for i in coords[:8]])
        a,b,c,d = [bool(chart_word & (1 << j)) for j in (2,4,5,6)]
        index = 0 if a else 1 if not c else 2 if not b else 3 if d else 4
        candidates = ([("weighted reversal", HARD, True)] if index == 4
                      else [(f"reversal {index+1}", REVERSED[index], False)])
    else:
        bit,ranks = next((b,r) for b,r in PRIMARY if not (word >> b) & 1)
        candidates = [(f"first unswapped node {bit}", ranks, False)]
    for name, ranks, weighted in candidates:
        count = 22 if weighted else 26-len(ranks)
        a,b,c = (F(411,176),F(3,4),F(19,8)) if weighted else (F(64,27),)*3
        rates = {t:a for t in reservoir(order[:32], count)}
        rates[center] = b
        rates.update({tips[i]:c for i in ranks})
        assert sum(rates.values()) == 64
        rows,num,den = ledger(order, rates)
        if num/den >= GUARANTEE:
            return dict(label_order=labels, pairing=pairing, rule=name, sparse_ranks=ranks,
                        rates={str(t):str(v) for t,v in sorted(rates.items())},
                        numerator=str(num), denominator=str(den), ratio=str(num/den),
                        denominator_leaf_tail="64", nodes=rows)
    raise AssertionError("No certificate for this labeling")


def reverse_bits(i, n):
    return int(f"{i:0{n}b}"[::-1],2)


def dyadic_maps(width):
    if width == 1:
        return [(0,)]
    half = width//2
    children = dyadic_maps(half)
    return [ordering for left in children for right in children
            for ordering in (left + tuple(half+i for i in right),
                             tuple(half+i for i in left) + right)]


def chart_labels(pairing, layout):
    left = [2*reverse_bits(i,3) for i in layout]
    coords = left + [(-1-left[pairing.index(i)]) % 16 for i in range(8)]
    return ([2*reverse_bits(i,5) for i in range(32)]
            + [1+4*reverse_bits(i,4) for i in range(16)]
            + [3+4*i for i in coords])


def hard_labels():
    return chart_labels(tuple(reversed(range(8))), (0,1,3,2,5,4,6,7))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--labels", type=Path, help="JSON array containing a permutation of 0 through 63")
    p.add_argument("--check", action="store_true", help="reproduce the literal example and run independent controls")
    args = p.parse_args()
    if args.check:
        from random import Random
        demo = certificate(hard_labels())
        saved = Path(__file__).with_name("worked_example.json")
        assert json.loads(saved.read_text()) == json.loads(json.dumps(demo))
        rng = Random(4471)
        assert F(demo["ratio"]) == GUARANTEE and demo["rule"] == "weighted reversal"
        maps = dyadic_maps(8)
        normalized = [g for g in maps if g[0] == 0]
        count = 0
        for pairing in maps:
            for layout in normalized:
                labels = chart_labels(pairing,layout)
                unit, shift = 2*(count % 32)+1, count % 64
                result = certificate([(unit*t+shift) % 64 for t in labels])
                assert tuple(result["pairing"]) == pairing
                count += 1
        assert count == 2048
        for _ in range(256):
            certificate(rng.sample(range(64),64))
        print("Literal example matched; all 2,048 normalized layouts and 256 fixed-seed labelings passed.")
    else:
        labels = json.loads(args.labels.read_text()) if args.labels else hard_labels()
        print(json.dumps(certificate(labels),indent=2))


if __name__ == "__main__":
    main()
