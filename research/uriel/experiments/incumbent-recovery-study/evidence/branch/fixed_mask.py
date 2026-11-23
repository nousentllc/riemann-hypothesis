"""Compute both original gain branches on one fixed cyclic retained set."""
import argparse
from fractions import Fraction as F
import importlib.util
import json
from math import ceil
from pathlib import Path


def gains(p, shift, positions):
    n = 32
    height = ceil(F(p**9, 2))
    top_level = p**8 // 4
    offset = F(top_level, 16)
    rank = 208
    curvature = 4 * 4 * 64 * (rank * 2**10)
    al = height - 2 * curvature
    thin = offset / n
    cap_hole = thin + curvature - shift
    cap_top = top_level + offset + curvature - shift
    assert cap_top > cap_hole >= 1 and al > 0
    odd = sum(v % 2 for v in positions)
    even = len(positions) - odd
    price = odd*(offset-shift) + n*(thin + 1 + curvature + rank)
    loss = n*rank**2*9 + len(positions)*81
    gamma = F(p, p**2-1)
    kept = odd_pos = head_credit = excluded = F(0)
    for s in positions:
        e = 1
        while True:
            u = F(al, p**e)
            on = ((s+e) % n) in positions
            cap = cap_top if on else cap_hole
            demand = max(F(0), u-cap)
            if e < n and on:
                excluded += demand
            else:
                kept += demand
            if s % 2:
                odd_pos += demand
            if e == 1:
                head_credit += (demand if on else 0) + (min(u,cap) if s%2==0 else 0)
            if u <= cap_hole:
                break
            e += 2
    g0 = kept - loss
    # Each odd-source minimum series equals its whole supply minus all positive demands.
    specialized = len(positions)*al*gamma - (odd*al*gamma-odd_pos) - loss - price
    recovery = max(F(0), max(g0,0)-specialized)
    tail = F(even*al, p*(p*p-1))
    control_cutoff = F(p**9, 2*top_level)
    assert g0>0 and price>0 and p**3 >= 2*control_cutoff
    assert max(0,price-head_credit-tail) <= recovery <= max(0,price-head_credit)
    adjacent = sum((s+1)%n in positions for s in positions)
    if adjacent==0:
        assert head_credit <= even*cap_hole
        assert price - even*cap_hole-tail <= recovery <= price
        assert recovery == price-(specialized-g0+price) and recovery>0
    return dict(g0=g0, specialized=specialized, price=price, excluded=excluded,
                head_credit=head_credit, tail=tail, recovery=recovery, odd=odd, edges=adjacent,
                share=recovery/(len(positions)*offset), lambda_unit=offset)


def compare_previous(mod, p, shift, positions, result):
    c = mod.Panel(n=32,p=p,log_height=9,top_level=p**8//4,
                  top_offset=F(p**8//4,16),shift=F(shift),curvature=F(218103808),
                  auxiliary_rank=F(208),dl1=F(1),dl2=F(1),pr1=F(1))
    prior = mod.evaluate(c, sorted(positions))
    assert result["g0"] == prior["g0"]
    assert result["specialized"] == prior["gU_minus_Pr"]
    assert result["recovery"] == prior["credit_over_U"]


def profile(labels):
    n = len(labels)
    r = [min(range(i,n,2),key=labels.__getitem__)%8 for i in (0,1)]
    tops = {t for t in range(n) if t%8 in r}
    base = min(range(n),key=labels.__getitem__)
    return r, tops, base


def run(previous=None):
    if previous:
        spec = importlib.util.spec_from_file_location("gain_reference", previous)
        reference = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(reference)
    labels = [list(range(32)), [(13+3*i)%32 for i in range(32)]]
    summaries = []
    for label_id, order in enumerate(labels):
        r,tops,base = profile(order)
        rotated = [order[(t-7)%32] for t in range(32)]
        _, rotated_tops, rotated_base = profile(rotated)
        assert rotated_tops == {(t+7)%32 for t in tops}
        allowed = {(r[0]-r[1])%8, (r[1]-r[0])%8}
        for p in (1009,10007):
            for j,shift in enumerate((68,140),1):
                holes, edges = [], []
                sample = {}
                for h in range(1,32,2):
                    inv = pow(h,-1,32)
                    positions = {(t-base)*inv%32 for t in tops}
                    shifted_positions = {(t-rotated_base)*inv%32 for t in rotated_tops}
                    assert positions == shifted_positions
                    row = gains(p,shift,positions)
                    if previous:
                        compare_previous(reference,p,shift,positions,row)
                    assert row["edges"] == (4 if h%8 in allowed else 0)
                    assert row["odd"] == 4 and row["g0"]>0
                    if h%8 in allowed:
                        assert row["specialized"]>row["g0"] and row["recovery"]==0
                        edges.append(h)
                    else:
                        assert row["g0"]>row["specialized"] and row["recovery"]>0
                        holes.append(h)
                    sample.setdefault(str(h%8),row)
                summaries.append(dict(labels=label_id, support_classes=r, fixed_mask=sorted(tops),
                                      least_base=base,p=p,j=j,holes=holes,adjacent=edges,by_residue=sample))
                assert len(holes)==len(edges)==8
    return dict(n=32, comparisons=128, rotations_checked=128, rows=summaries)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--previous",type=Path,help="optional authenticated previous study's cycles.py")
    ap.add_argument("--check",action="store_true",help="compare with saved output")
    args=ap.parse_args()
    serialized=json.dumps(run(args.previous),indent=2,default=str)+"\n"
    if args.check:
        assert Path(__file__).with_name("results.json").read_text()==serialized
        print("128 exact orbit/step/lift tests passed")
    else:
        print(serialized,end="")


if __name__ == "__main__":
    main()
