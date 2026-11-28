"""Rebuild the complete 32-residue root-hole panel and one rigorous capped upper bound."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ADVERSE = 8421923
INITIAL = (0, 64, 1431633984, 305397824, 715784256)


@lru_cache(None)
def exp_bounds(x):
    term = total = F(1)
    for n in range(1, 25):
        term *= x/n
        total += term
    return total, total + term*x/25/(1-x/26)


def tile_table():
    lines = []
    for k in (14, 15, 16):
        for width in (2, 4, 8, 16, 32):
            for count in range(1, min(k, width)+1):
                mu = F(32*count, k*width)
                lo, hi = exp_bounds(mu)
                for even in range(min(width//2, count)+1):
                    nu = F(32*even, k*width)
                    lhs, power = (100*nu, 2) if nu <= 1 else (10**13*nu**6, 13)
                    assert lhs < lo**power or lhs > hi**power
                    lines.append(f"{k} {width} {count} {even} {int(lhs > hi**power)}")
    return "\n".join(lines)+"\n"


def explicit_vertex():
    support = [1, 3, 4, 5, 6, 7, 9, 11, 13, 16, 17, 21, 25, 29]
    def components(t):
        n, d = 0, 1
        for s in (1, 2, 4, 8, 16):
            c = t%s
            even = (ADVERSE >> (s-1+c))&1
            if (t//s)%2 == even:
                continue
            node = [i for i in support if i%s == c]
            differences = {(u-v)%32 for u in node for v in node}
            n += 2*sum(h not in differences for h in range(s, 32, 2*s))
            d += 32//s
        return n, d
    weighted_n, weighted_d = 0, 0
    table = []
    for t in support:
        n, d = components(t)
        fifths = 4 if t == 6 else 12
        weighted_n += fifths*n
        weighted_d += fifths*d
        table.append([t, n, d, fifths])
    assert sum(row[-1] for row in table) == 160
    assert F(weighted_n, weighted_d) == F(6, 61)
    return table


def run():
    with TemporaryDirectory() as tmp:
        for name in ("threshold", "cycle_cover"):
            subprocess.run([os.environ.get("CXX", "c++"), "-std=c++17", "-O3",
                            str(HERE/f"{name}.cpp"), "-o", str(Path(tmp)/name)], check=True)
        cover = subprocess.check_output([str(Path(tmp)/"cycle_cover")], input=tile_table(), text=True)
        lines = cover.splitlines()
        assert lines[0] == "sets 43474 viable 43474"
        rows = [list(map(int,line.split())) for line in lines[1:-1]]
        assert len(rows) == 256
        missed = sum(65536-n for _,n,_,_ in rows)
        assert [int(lines[-1].split()[i]) for i in (1, 3, 5)] == [missed, max(65536-r[1] for r in rows), 0]
        assert missed == 332964
        samples = []
        for a, b, words in [(1, 10, (*INITIAL, 33315, ADVERSE)), (6, 61, (ADVERSE,))]:
            raw = subprocess.check_output([str(Path(tmp)/"threshold"), str(a), str(b),
                                           *map(str, words)], text=True)
            for line in raw.splitlines():
                word, ba, bb, total, positive, tied, best, emask, omask, holes, *hist = map(int, line.split())
                assert (ba, bb, total)==(1807,1807,3024572)
                assert sum(hist)==positive
                if word==ADVERSE:
                    assert (positive, tied, best) == ((0, 0, -48) if a==1 else (0, 2, 0))
                samples.append(dict(orientation=word, threshold=f"{a}/{b}", supports=total,
                                    above=positive, tied=tied, maximum_integer_excess=best,
                                    best_even_mask=emask,best_odd_mask=omask,best_root_holes=holes))
    return dict(root_panel=dict(affine_quotient_cases=len(rows)*65536,
                                all_labeled_cases=(1 << 31), orbit_multiplicity=128,
                                unique_cycles_supports=43474,
                                covered_representatives=len(rows)*65536-missed,
                                uncovered_representatives=missed,
                                covered_total=(len(rows)*65536-missed)*128,
                                rows_sha256=sha256(cover.encode()).hexdigest(),
                                first_uncovered_by_coarse_word=[(word, bot) for word,n,_,bot in rows if n<65536]),
                capped_profiles=samples, vertex_rows_t_num_den_fifths=explicit_vertex())


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check", action="store_true")
    args=p.parse_args()
    data=run()
    path=HERE/"results.json"
    text=json.dumps(data,indent=2)+"\n"
    if args.check:
        assert path.read_text()==text
    else:
        path.write_text(text)
    r=data["root_panel"]
    print(r["covered_representatives"],"of",r["affine_quotient_cases"],"covered by the homogeneous root-hole search.")
    print("The adverse cap relaxation has maximum 6/61 at orientation",ADVERSE)


if __name__=="__main__":
    main()
