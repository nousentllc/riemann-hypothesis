"""Independent global value certificate using only positive integral inclusion."""
from fractions import Fraction as F
import json
from pathlib import Path

from bands import FIRST, MAX_START, PrimeWindow, build_cells
from prime_mass import I, S, box


def certify(signal):
    # Initial cells have length 64, so the common intersection is nonempty.
    starts = list(range(FIRST, MAX_START+1, 64))
    vals = [signal.band(F(s))[0] for s in starts]
    best_low = max(v.lo for v in vals)
    least_hi = min(v.hi for v in vals)
    highest_upper, least_lower = 0, None
    stack = [(F(a),F(b),0) for a,b in zip(starts,starts[1:])]
    terminal = processed = depth = 0
    tol = box(F(1,1_000_000)).lo
    while stack:
        l, r, level = stack.pop()
        processed += 1
        depth = max(depth,level)
        m = (l+r)/2
        v, _ = signal.band(m)
        best_low, least_hi = max(best_low,v.lo), min(least_hi,v.hi)
        span, _ = signal.enclosed_band(l,r)
        if span.hi > best_low+tol or span.lo < least_hi-tol:
            assert level < 32
            stack.extend([(l,m,level+1),(m,r,level+1)])
        else:
            terminal += 1
            highest_upper = max(highest_upper,span.hi)
            least_lower = span.lo if least_lower is None else min(least_lower,span.lo)
    assert highest_upper-best_low <= tol and least_hi-least_lower <= tol
    return {'minimum':I(least_lower,least_hi).pair(), 'maximum':I(best_low,highest_upper).pair(),
            'boxes_visited':processed,'terminal_partition_cells':terminal,'maximum_bisection_depth':depth}


def run():
    out={}
    cells=build_cells()
    published=json.loads(Path(__file__).with_name('results.json').read_text())['rows']
    for j in (2,3):
        theta=str(F(j,4))
        row=certify(PrimeWindow(j,cells))
        for side in ('minimum','maximum'):
            coarse=list(map(F,row[side]))
            tight=list(map(F,published[theta]['continuous_search'][side]['mass']))
            assert coarse[0]<=tight[0]<=tight[1]<=coarse[1]
        out[theta]=row
    return out


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
