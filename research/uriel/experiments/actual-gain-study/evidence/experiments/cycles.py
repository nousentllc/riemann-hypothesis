"""Exact served-orbit gain and demand on finite cyclic controls."""
from collections import Counter
from dataclasses import dataclass, replace
from fractions import Fraction as F
from math import ceil
import argparse
import json
from pathlib import Path


@dataclass(frozen=True)
class Panel:
    n: int = 8
    p: int = 5
    log_height: int = 5  # 2a = p^log_height
    top_level: int = 150
    top_offset: F = F(64)
    shift: F = F(6)
    curvature: F = F(2)
    auxiliary_rank: F = F(1)
    spread: F = F(1)
    dl1: F = F(1, 64)
    dl2: F = F(1, 64)
    pr1: F = F(1, 16)

    @property
    def integer_height(self):
        return ceil(F(self.p**self.log_height, 2))

    @property
    def thin(self):
        return self.top_offset / self.n


def ray_excess(height, cap, p, n, r):
    """Sum (height/p^(r+kn) - cap)_+ on one residue class of exponents."""
    assert height >= 0 and cap >= 0
    term = F(height, p**r)
    ratio = F(1, p**n)
    if cap == 0:
        return term / (1-ratio)
    value = F(0)
    while term > cap:
        value += term-cap
        term *= ratio
    return value


def cycle_terms(c, tops):
    assert 0 < len(tops) <= c.n and c.n % 2 == 0
    assert all(0 <= s < c.n for s in tops)
    a = F(c.integer_height)
    al = a - 2*c.curvature
    assert al >= 0
    gamma = F(c.p, c.p**2-1)
    result = Counter()
    for s in tops:
        for r in range(1, c.n, 2):
            dest = (s+r) % c.n
            fill = c.top_level+c.top_offset if dest in tops else c.thin
            fill_g = fill-c.shift
            cap = fill_g+c.curvature
            assert min(fill, fill_g, cap) >= 0
            ray = F(1, c.p**r) / (1-F(1,c.p**c.n))
            positive = ray_excess(al, cap, c.p, c.n, r)
            # On an even orbit odd r < n never returns to the start.
            first = max(F(0), al/c.p**r-cap) if dest in tops else F(0)
            result["g0_positive_before_exclusions"] += positive
            result["first_excluded"] += first
            result["later_positive_arrivals_at_other_top"] += positive-first if dest in tops else 0
            result["askP"] += ray_excess(a, fill, c.p, c.n, r)
            result["askG"] += ray_excess(a, fill_g, c.p, c.n, r)
            if s % 2:
                result["odd_min"] += al*ray-positive
            else:
                result["even_min_fill"] += a*ray-ray_excess(a, fill, c.p, c.n, r)
    result["gross"] = len(tops)*al*gamma
    return result


def independently_sum(c, tops):
    """Scan odd exponents directly and close the remaining geometric series at once."""
    a = F(c.integer_height)
    al = a-2*c.curvature
    fills = [c.top_level+c.top_offset if t in tops else c.thin for t in range(c.n)]
    caps = [v-c.shift+c.curvature for v in fills]
    fills_g = [v-c.shift for v in fills]
    positive_caps = [v for v in fills+caps+fills_g if v > 0]
    h = max(a, al)
    r = 1
    out = Counter()
    # Include the whole first lap before switching to periodic tail evaluation.
    while r < c.n or (positive_caps and h / c.p**r > min(positive_caps)):
        for s in tops:
            dest = (s+r) % c.n
            exc = max(F(0), al/c.p**r-caps[dest])
            out["g0_positive_before_exclusions"] += exc
            if dest in tops and r < c.n:
                out["first_excluded"] += exc
            if dest in tops and r >= c.n:
                out["later_positive_arrivals_at_other_top"] += exc
            out["askP"] += max(0,a/c.p**r-fills[dest])
            out["askG"] += max(0,a/c.p**r-fills_g[dest])
            if s % 2:
                out["odd_min"] += min(al/c.p**r, caps[dest])
            else:
                out["even_min_fill"] += min(a/c.p**r, fills[dest])
            out["gross"] += al/c.p**r
        r += 2
    for s in tops:
        for d in range(r, r+c.n, 2):
            dest=(s+d) % c.n
            ray=F(1, c.p**d)/(1-F(1,c.p**c.n))
            out["gross"] += al*ray
            if caps[dest] == 0:
                out["g0_positive_before_exclusions"] += al*ray
                if dest in tops:
                    out["later_positive_arrivals_at_other_top"] += al*ray
            elif s % 2:
                out["odd_min"] += al*ray
            if fills[dest] == 0:
                out["askP"] += a*ray
            elif not s%2:
                out["even_min_fill"] += a*ray
            if fills_g[dest] == 0:
                out["askG"] += a*ray
    return out


def evaluate(c, top_indices):
    tops=frozenset(top_indices)
    z=cycle_terms(c,tops)
    assert z == independently_sum(c,tops), (c,tops,z,independently_sum(c,tops))
    odd=sorted(t for t in tops if t%2)
    even=sorted(tops-set(odd))
    dl=c.dl1*c.n*c.auxiliary_rank**2*c.log_height+c.dl2*len(tops)*c.log_height**2
    pr_fixed=c.pr1*c.n*(c.thin+c.spread+c.curvature+c.auxiliary_rank)
    pr_variable=(c.top_offset-c.shift)*len(odd)
    g0=z["g0_positive_before_exclusions"]-z["first_excluded"]-dl
    gU=z["gross"]-z["odd_min"]-dl
    u=gU-pr_variable-pr_fixed
    maximum=max(u,g0,0)
    direct_credit=max(g0,0)
    charge_rows=[]
    matched=F(0)
    edge_tax=F(0)
    for y in odd:
        distance=min(((y-x)%c.n for x in even),default=0)
        vertical=F(c.integer_height,c.p**distance) if distance else F(0)
        clip=min(c.top_offset,max(0,vertical-c.top_level)) if distance else F(0)
        if distance:
            matched += min(c.top_level+c.top_offset,vertical)
            edge_tax += min(c.top_level, vertical)
        charge_rows.append({"position":y,"distance":distance,"clip":clip,
                            "signed":c.top_offset-c.shift-clip})
    unused=z["even_min_fill"]-matched
    assert unused >= 0
    kink=sum(row["signed"] for row in charge_rows)-unused
    exact_difference=u-g0
    assert exact_difference == (z["gross"]-z["odd_min"]-
        z["g0_positive_before_exclusions"]+z["first_excluded"]-pr_variable-pr_fixed)
    return {"tops":sorted(tops),"a":c.integer_height,"g0":g0,"gU":gU,"Pr":pr_variable+pr_fixed,
            "Pr_variable":pr_variable,"Pr_fixed":pr_fixed,"gU_minus_Pr":u,"dl":dl,
            "gain_served":maximum,"gain_unserved":direct_credit,
            "winners":[name for name,value in (("U",u),("G0",g0),("zero",0)) if value==maximum],
            "askP":z["askP"],"askG":z["askG"],"gapP":z["askP"]-maximum,"gapG":z["askG"]-maximum,
            "gapP_using_U":z["askP"]-u,"credit_over_U":maximum-u,
            "Sv_one_lift":ceil(max(0,u-direct_credit)),
            "raw_increment_over_unserved":maximum-direct_credit,
            "g0_before_dl":g0+dl,"excluded":z["first_excluded"],
            "repeat_positive":z["later_positive_arrivals_at_other_top"],
            "odd_rows":charge_rows,"nearest_even_tax":edge_tax,"unused":unused,"kink":kink,
            "kink_positive":max(0,kink),"kink_to_nominal":kink/(len(odd)*c.top_offset) if odd and c.top_offset else None}


def bulk(n,p):
    a=F(p**3,2)
    b=int(a/(2*p))
    return Panel(n=n,p=p,log_height=3,top_level=b,top_offset=F(b,4),
                 shift=F(0),curvature=F(0),dl1=F(0),dl2=F(0),pr1=F(0))


def as_json(v):
    if isinstance(v,F):
        return str(v)
    raise TypeError(type(v))


def one_orbit_tax(panel, result, lifts, threshold_residual=0, degree=0, ep=0):
    """High-regime tIf and tauP with exactly one served orbit."""
    common_t = 2 * panel.n * panel.curvature + threshold_residual
    t_value = result["nearest_even_tax"] + common_t
    natural_ceiling = max(0, ceil(t_value))
    orbit_tax = natural_ceiling + degree + 1
    return {
        "nearest_even_component": result["nearest_even_tax"],
        "common_t_residual": common_t,
        "t": t_value,
        "t_natural_ceiling": natural_ceiling,
        "Dp": degree,
        "ep": ep,
        "lift_count": lifts,
        "prime_tax": ep + lifts * orbit_tax,
        "per_lift_tax_equal_allocation": orbit_tax + F(ep, lifts),
        "per_lift_taxed_gap": result["gapP"] + orbit_tax + F(ep, lifts),
    }


def rank_compatible_controls():
    n, k, m, t = 32, 64, 2, 71
    rank = k + m*(t+1)
    delta = rank*m**10
    sc = 4*k*delta
    assert k%2 == m%2 == 0 and t%2 == 1
    assert 2 <= m and m+3 <= k and k+m-1+5 <= t and 3*m < t
    assert m <= 2*n <= k and m*m <= rank <= sc and sc >= 100
    records = []
    for p in (1009,10007):
        scale_height = F(p**9,2)
        level = int(scale_height/(2*p))
        for tops in ((0,3),(3,4)):
            lifts = []
            for j in range(1,m+1):
                shift = F(k+(2*j-1)*(t+1),2)
                model = Panel(n=n,p=p,log_height=9,top_level=level,top_offset=F(level,16),
                              shift=shift,curvature=F(4*sc),auxiliary_rank=F(rank),
                              dl1=F(1),dl2=F(1),pr1=F(1))
                assert 0 <= shift <= rank and rank+1 <= model.thin
                out = evaluate(model,tops)
                assert out["winners"] == (["G0"] if tops==(0,3) else ["U"])
                lifts.append(out)
            # tauP is independent of j; the two demands and two selected gains are summed.
            tax = one_orbit_tax(model,lifts[0],m)
            unshifted_gap = sum(row["gapP"] for row in lifts)
            records.append({"p":p,"tops":list(tops),"lambda":model.top_offset,
                            "lifts":lifts,"prime_tax":tax["prime_tax"],"edge_tax":tax["nearest_even_component"],
                            "unshifted_gap_sum":unshifted_gap,"taxed_prime_gap":unshifted_gap+tax["prime_tax"]})
    return {"n":n,"k":k,"m":m,"t":t,"Nm":rank,"Delta":delta,"Sc":sc,"cG":4*sc,"records":records}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-masks",type=Path,help="also save exact per-mask controls")
    args=parser.parse_args()
    c=Panel()
    all_rows=[evaluate(c,[t for t in range(c.n) if (mask >> t)&1]) for mask in range(1,2**c.n)]
    if args.all_masks:
        args.all_masks.write_text(json.dumps(all_rows,default=as_json,indent=2)+"\n")
    named={str(t):evaluate(c,t) for t in ((0,),(3,),(0,3),(3,4),(0,1))}
    expensive={str(t):evaluate(replace(c,dl1=F(1000)),t) for t in ((0,),(3,))}
    g=named[str((3,4))]
    tie=(g["gU"]-g["Pr_variable"]-g["g0"])/(c.n*(c.thin+c.spread+c.curvature+c.auxiliary_rank))
    assert tie >= 0
    boundary=evaluate(replace(c,pr1=tie),(3,4))
    boost=evaluate(replace(c,pr1=tie+1),(3,4))
    long=replace(c,log_height=15,top_level=0,top_offset=F(1),shift=F(0),curvature=F(0))
    repeated=evaluate(long,(0,1))
    zero_caps=evaluate(replace(c,top_level=0,top_offset=F(0),shift=F(0),curvature=F(0)),(0,1))
    assert zero_caps["askP"] == zero_caps["askG"] == 2*F(c.p*c.integer_height,c.p**2-1)
    growing=[{"n":n,"p":p,"tops":list(t),"result":evaluate(bulk(n,p),t)}
             for n in (8,16,32) for p in (5,101,1009) for t in ((0,3),(3,4))]
    coupled = []
    lift_rounding = []
    for p in (101,1009):
        height=F(p**5,2)
        level=int(height/(2*p))
        model=Panel(n=32,p=p,log_height=5,top_level=level,top_offset=F(level,16),
                    shift=F(15),curvature=F(128),auxiliary_rank=F(44),spread=F(1),
                    dl1=F(1),dl2=F(1),pr1=F(1))
        assert model.auxiliary_rank == 16+2*(13+1)
        assert model.shift == F(16+(2*1-1)*(13+1),2)
        assert model.shift <= model.curvature/4
        assert model.auxiliary_rank+1 <= model.thin
        for t in ((0,3),(3,4)):
            out=evaluate(model,t)
            coupled.append({"n":32,"p":p,"tops":list(t),"lambda":model.top_offset,"result":out})
            second=evaluate(replace(model,shift=F(16+3*(13+1),2)),t)
            increments=[r["raw_increment_over_unserved"] for r in (out,second)]
            lift_rounding.append({"p":p,"tops":list(t),"increments":increments,
                                  "Sv":ceil(sum(increments)),"sum_of_ceilings":sum(map(ceil,increments))})
    tested=[named[str((0,3))],named[str((3,4))]]
    sum_max=sum(row["gain_served"] for row in tested)
    max_sum=max(sum(row["gU_minus_Pr"] for row in tested),sum(row["g0"] for row in tested),0)
    aggregate={"sum_before_comparing":max_sum,"sum_of_orbit_maxima":sum_max,
               "credit_lost_by_mixing_orbits":sum_max-max_sum}
    assert all(row["gU_minus_Pr"]-row["g0"] ==
               expensive[t]["gU_minus_Pr"]-expensive[t]["g0"]
               for t,row in named.items() if t in expensive)
    assert all(v["winners"]==["zero"] for v in expensive.values())
    assert boundary["winners"]==["U","G0"] and boost["winners"]==["G0"]
    assert repeated["repeat_positive"] > 0
    assert [named[str(t)]["winners"] for t in ((0,),(3,),(0,3),(3,4))] == [["U"],["G0"],["G0"],["U"]]
    assert [named[str(t)]["odd_rows"][0]["signed"] for t in ((0,3),(3,4),(0,1))] == [58,58,-6]
    assert all(r["result"]["winners"] == (["G0"] if r["tops"]==[0,3] else ["U"]) for r in coupled)
    for row in growing:
        out=row["result"]
        assert min(out["excluded"],out["gapP_using_U"]) == out["gapP"]
        assert out["gapP"]==0 if row["tops"]==[0,3] else out["gapP"]>0
    tax_pair = {str(t):one_orbit_tax(c,named[str(t)],1) for t in ((0,3),(3,4))}
    # The exact ceiling difference may change with the fractional part of a shared residual.
    differences = set()
    for residual in (0,F(1,100),F(1,2),F(99,100),1):
        left,right = [one_orbit_tax(c,r,1,residual) for r in tested]
        differences.add(left["prime_tax"]-right["prime_tax"])
    assert differences == {12,13}
    summary={
        "primary_coefficients":c.__dict__,
        "mask_count":len(all_rows),
        "strict_and_tied_wins":dict(Counter("+".join(r["winners"]) for r in all_rows)),
        "sign_of_unshifted_gap":dict(Counter("positive" if r["gapP"]>0 else "negative" if r["gapP"]<0 else "zero" for r in all_rows)),
        "primary_cases":named,"common_subtraction_controls":expensive,"tie_coefficient":tie,
        "rank_coupled_followup":coupled,"rank_compatible_followup":rank_compatible_controls(),
        "two_orbit_aggregation":aggregate,
        "two_lift_rounding":lift_rounding,"tax_pair":tax_pair,
        "tax_difference_with_shared_residual":sorted(differences),"zero_caps":zero_caps,
        "positive_tie":boundary,"above_tie":boost,"later_lap":repeated,"growing_bulk":growing}
    print(json.dumps(summary,default=as_json,indent=2))


if __name__=="__main__":
    main()
