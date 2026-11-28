"""Certify the optimum of the frozen support decision with three or arbitrary rates."""
import argparse
from fractions import Fraction as F
from functools import cache
from itertools import product
import json
from pathlib import Path

BETA = F(5190,10381)
HALF = F(1,2)
CL, CU = F(23920857150,10**10), F(23920857151,10**10)
BL, BU = F(7062641303,10**10), F(7062641305,10**10)
ORDINARY_C = F(299,125)
ORDINARY_B = 64-26*ORDINARY_C
HARD = 0xd101
PRIMARY = (0x070f,0x0331,0x07d1,0x0d71,0x3101,0x5101,0xd107)
REVERSED = (0x1301,0x0d11,0x1501,0x5101)
P_ORDER = (0,2,5,6,1,3,4)
DELETIONS = ((3,6,7),(3,5,7),(1,6,7))

@cache
def reduced_log(x):
    """Exact enclosure of log x for 1 <= x <= 2 by the atanh series."""
    assert 1 <= x <= 2
    t = (x-1)/(x+1)
    p = t
    low = F(0)
    for j in range(26):
        low += 2*p/(2*j+1)
        p *= t*t
    return low, low+2*p/(53*(1-t*t))

@cache
def logarithm(x):
    x = F(x)
    assert x > 0
    power = 0
    while x < 1:
        x *= 2
        power -= 1
    while x >= 2:
        x /= 2
        power += 1
    low, high = reduced_log(x)
    l2,h2 = reduced_log(F(2))
    return low+min(power*l2,power*h2), high+max(power*l2,power*h2)

def tile_interval(mu,nu,beta=None):
    if beta is None:
        beta = BETA if nu > 1 else HALF
    l10,h10 = logarithm(10)
    ln,hn = logarithm(nu)
    return l10-mu+beta*ln,h10-mu+beta*hn

def sparse_anchor(c,b,beta=HALF):
    return tile_interval((b+5*c)/32,b/32,beta)

def endpoint(c,b,three=False):
    if three:
        return (1280+2012*c-20*b)/(35968+10016*c+868*b)
    return 116*c/(2112+254*c+32*b)

def swap(word,i):
    prefix = out = 0
    for shift in (2,1,0):
        bit = (i >> shift) & 1
        out = 2*out+(bit ^ ((word >> prefix)&1))
        prefix = 2*prefix+1+bit
    return out

def rev(i,k):
    return int(f"{i:0{k}b}"[::-1],2)

def cost(mask, width, coords=None):
    if width == 1:
        return -mask
    lo = mask % (1 << (width//2))
    hi = mask >> (width//2)
    if coords is None:
        d = max(0,width//2-2*lo.bit_count()*hi.bit_count())
        left = right = None
    else:
        s = {c for i,c in enumerate(coords) if mask >> i & 1}
        d = sum(all((t+h)%width not in s for t in s) for h in range(1,width,2))
        left = [i//2 for i in coords[:width//2]]
        right = [i//2 for i in coords[width//2:]]
    return hi.bit_count()*(20*d-width)+cost(lo,width//2,left)+cost(hi,width//2,right)

def ordinary_score(mask,p,coords=None):
    n = mask.bit_count()
    pairs = sum((mask>>i & 1)*(mask>>(8+p[i]) & 1) for i in range(8))
    d = 16-2*(n-pairs)
    reservoir = {4:-362,5:-331,7:-195}[n]
    return reservoir+cost(mask,16,coords)-65+n*(20*d-96)

def ordinary_minimum():
    scores = []
    for word in range(127):
        p = [swap(word,i) for i in range(8)]
        row = next(j for j,b in enumerate(P_ORDER) if not(word>>b & 1))
        scores.append(ordinary_score(PRIMARY[row],p))
    for word in range(128):
        if swap(word,0) != 0:
            continue
        a,b,c,d = (word>>j & 1 for j in (2,4,5,6))
        idx = 0 if a else 1 if not c else 2 if not b else 3 if d else 4
        if idx == 4:
            continue
        left = [2*rev(swap(word,i),3) for i in range(8)]
        coords = left+[(-1-u)%16 for u in reversed(left)]
        scores.append(ordinary_score(REVERSED[idx],list(range(7,-1,-1)),coords))
    assert len(scores) == 142 and min(scores) == 5
    return min(scores)

def groups(mask,hard,split,deleted):
    """Canonical 64 ranks. 0=absent, 1=main c, 2=singleton b, 3=reservoir adjustment."""
    k = 22 if hard else 26-mask.bit_count()
    high,low = {19:(16,3),21:(15,6),22:(16,6)}[k]
    short = {0,8,12} if low == 3 else {0}|{8+j for j in range(8) if j not in deleted}
    dense = [1]*high + [0]*(16-high) + [int(j in short) for j in range(16)]
    if hard:
        if split:
            dense[16] = 3
        else:
            dense = [3*i for i in dense]
    return dense + [2] + [0]*15 + [(mask>>i)&1 for i in range(16)]

def forms(shape):
    """All (mean total, mean even) as linear forms in (c,b,a) on this support."""
    out = set()
    def mean(types,w):
        return tuple(F(types.count(i),w) for i in (1,2,3))
    for w in (2,4,8,16,32,64):
        for i in range(0,64,w):
            seg = shape[i:i+w]
            if any(seg):
                out.add((mean(seg,w),mean(seg[:w//2],w)))
    for t in set(shape)-{0}:
        out.add((mean([t],1),mean([t],2)))
    return out

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def adjustment(c,b,split):
    return 64-26*c-b if split else (64-5*c-b)/22

def check_shapes(split,coverage,c=CL,b=BU):
    all_forms = set()
    for ds in DELETIONS:
        all_forms.update(forms(groups(HARD,True,split,ds)))
    rates = (c,b,adjustment(c,b,split))
    assert all(0<x<F(12,5) for x in rates)
    minimum = min(tile_interval(dot(m,rates),dot(v,rates))[0] for m,v in all_forms)
    assert minimum > 0
    # Bound all other constraints on a rational rectangle enclosing the exact corner.
    special = {((1,0,0),(HALF,0,0)),
               ((F(5,32),F(1,32),0),(0,F(1,32),0))}
    lo = (CL,BL,adjustment(CU,BU,split))
    hi = (CU,BU,adjustment(CL,BL,split))
    residual = min(tile_interval(dot(m,hi),dot(v,lo))[0] for m,v in all_forms-special)
    assert residual > 0
    return {"distinct_forms":len(all_forms),"ordinary_mark_forms":coverage,
            "smallest_log_slack":float(minimum),
            "corner_log_slack_excluding_two_active_forms":float(residual)}

def all_ordinary():
    fam = set()
    for mask,ds in product(set(PRIMARY+REVERSED),DELETIONS):
        fam.update(forms(groups(mask,False,False,ds)))
    a = (ORDINARY_C,ORDINARY_B,0)
    assert all(tile_interval(dot(m,a),dot(v,a))[0]>0 for m,v in fam)
    s0 = ordinary_minimum()
    j = ORDINARY_C*s0+65*(ORDINARY_C-ORDINARY_B)
    maxq = (562+7*127)*ORDINARY_C+65*ORDINARY_B
    return len(fam), F(1,10)+j/(10*maxq)

def literal():
    """Compute coefficients by direct differences for the tight prior labeling."""
    g = (0,1,3,2,5,4,6,7)
    left = [2*rev(i,3) for i in g]
    z = left+[(-1-i)%16 for i in reversed(left)]
    order = ([2*rev(i,5) for i in range(32)] + [1+4*rev(i,4) for i in range(16)]
             + [3+4*i for i in z])
    # On this literal labeling, the earlier reservoir deletes ranks {1,6,7}.
    kind = groups(HARD,True,True,DELETIONS[2])
    live = {t for t,k in zip(order,kind) if k}
    assert len(live) == 28
    out = {t:[0,1] for t in live}
    for w in (64,32,16,8,4,2):
        stride = 64//w
        for k in range(0,64,w):
            seats = set(order[k:k+w]) & live
            missing = sum(all((t+stride*h)%64 not in seats for t in seats)
                          for h in range(1,w,2))
            for t in seats & set(order[k+w//2:k+w]):
                out[t][0] += 2*missing
                out[t][1] += w
    sparse = set(order[48:]) & live
    dense = set(order[:32]) & live
    assert [sum(out[t][j] for t in sparse) for j in range(2)] == [96,583]
    assert [sum(out[t][j] for t in dense) for j in range(2)] == [20,562]
    single,adjusted = order[32],order[16]
    assert out[single] == [0,65] and out[adjusted] == [0,33]
    # At both ends of the enclosing interval certify all residual coefficients.
    for z0 in (F(1,10),F(11,100)):
        for t in live-{single,adjusted}:
            p,q=out[t]
            assert p-z0*(q-33) > (32*z0/14 if t in sparse else 0)
    return {"rates_in_physical_order":[[t,*out[t]] for t in sorted(live)],
            "sparse_sites":sorted(sparse),"singleton":single,"second_adjustment":adjusted}

def run():
    assert tile_interval(CL,CL/2,BETA)[0]>0 and tile_interval(CU,CU/2,BETA)[1]<0
    assert sparse_anchor(CL,BL)[1]<0 and sparse_anchor(CU,BU)[0]>0
    coverage, ordinary_lower = all_ordinary()
    data = {"minimum_source_r":1730,"minimum_source_beta":str(BETA),
            "c_interval":list(map(str,(CL,CU))),"b_interval":list(map(str,(BL,BU))),
            "ordinary_uniform_lower":str(ordinary_lower),"adverse_label":literal()}
    for name,split in (("three_common_rates",False),("arbitrary_individual_rates",True)):
        proof = check_shapes(split,coverage)
        lower = endpoint(CL,BU,three=not split)
        upper = endpoint(CU,BL,three=not split)
        assert ordinary_lower>upper>lower
        proof.update(lower=str(lower),upper=str(upper),gap_percentage_points=float(100*(upper-lower)),
                     attained_rate_vector=list(map(str,(CL,BU,adjustment(CL,BU,split)))))
        data[name]=proof
    # An outer envelope for any one fixed epsilon. Beta can be any source exponent.
    c_hi = F('2.392096617')
    c_lo = F('2.392096615')
    b_lo = F('0.70599524')
    assert tile_interval(c_lo,c_lo/2,HALF)[0]>0 and tile_interval(c_hi,c_hi/2,HALF)[1]<0
    assert sparse_anchor(c_lo,b_lo,BETA)[1]<0
    data["one_epsilon_upper"] = str(endpoint(c_hi,b_lo))
    data["cap_only_upper"] = str(endpoint(F(12,5),0))
    check_shapes(True,coverage,F(299,125),F(707,1000))
    data["simple_feasible_ratio"] = str(endpoint(F(299,125),F(707,1000)))
    return data

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check",action="store_true")
    args = ap.parse_args()
    result=run()
    serialized=json.dumps(result,indent=2)+"\n"
    path=Path(__file__).with_name("results.json")
    if args.check:
        assert serialized==path.read_text()
    else:
        path.write_text(serialized)
    for name in ("three_common_rates","arbitrary_individual_rates"):
        r=result[name]
        print(name, "percent interval", *(round(100*float(F(r[k])),11) for k in ("lower","upper")))

if __name__ == "__main__":
    main()
