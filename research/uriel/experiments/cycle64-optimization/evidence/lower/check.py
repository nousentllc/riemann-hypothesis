"""Proof-producing driver for the two-tip family and the exact-window refinement."""
import argparse
from fractions import Fraction as F
from functools import cache
from importlib.util import module_from_spec, spec_from_file_location
import json
import math
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
U, CAP = 8, 19
THRESHOLDS = ((1012, 10000), (103, 1000), (105, 1000), (11, 100))
spec = spec_from_file_location("frozen", HERE.parent / "rates" / "verify.py")
frozen = module_from_spec(spec)
spec.loader.exec_module(frozen)


@cache
def exp_bounds(x):
    """Taylor partial sum and geometric upper bound, all operations rational."""
    term = low = F(1)
    for k in range(1, 26):
        term *= x / k
        low += term
    tail = (term*x/26) / (1-x/27)
    return low, low+tail


def enough(nu, bound):
    if nu <= 1:
        return 100*nu > bound**2
    return 10**13*nu**6 > bound**13


def floors():
    """Locate the first passing even mass, then prove each side by rational bounds."""
    lines = []
    for width in (2, 4, 8, 16, 32, 64):
        for mass in range(1, min(512, width*CAP)+1):
            unit = U*width
            mu = F(mass, unit)
            b = math.exp(float(mu))/10
            first = 1+math.floor(unit*max(b**2, b**(13/6)))
            low, high = exp_bounds(mu)
            assert enough(F(first,unit),high)
            assert not enough(F(first-1,unit),low)
            lines.append(f"{width} {mass} {first}")
    for ticks in range(1,CAP+1):
        mu = F(ticks,U)
        assert enough(mu/2, exp_bounds(mu)[1])
    return "\n".join(lines)+"\n"


def weighted_window():
    """An independent, slightly less wasteful use of the source's tile count."""
    c, b = F("2.392096615"), F(".706267")
    a = 64-26*c-b
    rates = c,b,a
    signatures = set()
    for deletions in frozen.DELETIONS:
        signatures |= frozen.forms(frozen.groups(frozen.HARD,True,True,deletions))
    weighted, standard = [], []
    for total,even in sorted(signatures):
        mu = frozen.dot(total,rates)
        nu = frozen.dot(even,rates)
        if frozen.tile_interval(mu,nu)[0] > 0:
            standard.append((mu,nu))
        else:
            assert frozen.tile_interval(mu,nu,F(1,2))[0] > 0
            assert nu*F(54,67)**2 < 1
            weighted.append((mu,nu))
    val = frozen.endpoint(c,b)
    ordinary = frozen.all_ordinary()[1]
    assert val<=ordinary and max(rates)<F(12,5)
    return dict(rates=list(map(str,rates)), ratio=str(val), percent=100*float(val),
                ordinary_ratio=str(ordinary), number_of_forms=len(signatures),
                conventional_pass=len(standard),
                needs_source_prefactor=[[str(m),str(n)] for m,n in weighted],
                worst_h_ratio_bound="54/67")


def direct_replay(record, num, den):
    """Recheck marks and differences in literal physical coordinates."""
    witness = record["rescued_witness"]
    order = witness["physical_order"]
    ticks = witness["rate_ticks_in_tree_order"]
    assert sorted(order)==list(range(64)) and sum(ticks)==512
    assert all(0<=x<=CAP for x in ticks)
    recovery, exposure = 0, sum(ticks)
    omitted = 0
    for w in (2,4,8,16,32,64):
        stride = 64//w
        for b in range(0,64,w):
            pts = {order[i] for i in range(b,b+w) if ticks[i]}
            if not pts:
                continue
            assert all((t-order[b])%stride==0 for t in pts)
            assert all((t-order[b])%(2*stride)==0 for t in order[b:b+w//2])
            total = sum(ticks[b:b+w])
            even = sum(ticks[b:b+w//2])
            assert enough(F(even,8*w),exp_bounds(F(total,8*w))[1])
            missing = sum(all((t+h*stride)%64 not in pts for t in pts)
                          for h in range(1,w,2))
            inc = 2*missing*(total-even)
            if (w,b) in ((64,0),(32,0)):
                omitted += inc
            recovery += inc
            exposure += w*(total-even)
    ratio = F(recovery,exposure)
    assert den*(recovery-omitted)-num*exposure == witness["lower_integer_margin"]
    assert ratio>=F(num,den)
    witness.update(p_ticks=recovery,q_ticks=exposure,root_and_dense_parent_bonus_ticks=omitted,
                   actual_ratio=str(ratio),actual_percent=100*float(ratio))
    return witness


@cache
def orders(width):
    if width == 1:
        return ((0,),)
    return tuple(tuple([2*i+p for i in left]+[2*i+1-p for i in right])
                 for left in orders(width//2) for right in orders(width//2) for p in (0,1))


def frozen_crosswalk():
    """Execute the two historical reflection branches on all normalized D orders."""
    hard = []
    for index,coords in enumerate(orders(16)):
        if coords[0] != 0:
            continue
        pairing = tuple(coords[8:].index(15-i) for i in coords[:8])
        if pairing != tuple(range(7,-1,-1)):
            continue
        g = tuple(frozen.rev(i//2,3) for i in coords[:8])
        switches = next(w for w in range(128) if tuple(frozen.swap(w,i) for i in range(8))==g)
        a,b,c,d = ((switches>>j)&1 for j in (2,4,5,6))
        if not a and c and b and not d:
            hard.append((index,list(coords),switches))
    assert len(hard)==1
    return hard[0]


def run():
    marks = floors()
    with TemporaryDirectory() as tmp:
        exe = Path(tmp)/"search"
        subprocess.run(["c++","-std=c++17","-O3",str(HERE/"support.cpp"),"-o",str(exe)],check=True)
        searches=[]
        for num,den in THRESHOLDS:
            trial = subprocess.run([str(exe),str(num),str(den)],input=marks,
                                   check=True,capture_output=True,text=True)
            record = json.loads(trial.stdout)
            assert record["charts"]==16384 and record["local_shapes"]==1806
            assert record["single_pass"]<=record["either_pass"]
            direct_replay(record,num,den)
            searches.append(record)
    index,coords,switches=frozen_crosswalk()
    unresolved=searches[0]["full_dense_cross_on_coarse_misses"]
    combined_residual=sum(256**2-row[2] for row in unresolved if row[0]==index)
    return dict(fixed_support_literal_window=weighted_window(), sparse_search=searches,
                frozen_crosswalk=dict(hard_index=index,coordinates=coords,switches=switches,
                    steps_still_uncovered=[row[1] for row in unresolved if row[0]==index],
                    all_chart_tuples=2**30, combined_residual_at_10_12_percent=combined_residual))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=run()
    text=json.dumps(result,indent=2)+"\n"
    dest=HERE/"results.json"
    if args.check:
        assert dest.read_text()==text
    else:
        dest.write_text(text)
    print(text,end="")


if __name__=="__main__":
    main()
