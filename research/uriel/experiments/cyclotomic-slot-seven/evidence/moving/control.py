"""Controls for finite even-comparison costs. No cohomology values are sampled."""
import itertools
import json
from fractions import Fraction


def finite_costs():
    rows=[]
    tests=0
    for H in range(5):
        for t in range(7):
            count=max(0,t-1)
            # Every profile here is allowed by the componentwise comparison
            # against the constant companion H, including every boundary value.
            sums=[sum(v) for v in itertools.product(range(H+2),repeat=count)]
            tests+=len(sums)
            assert max(sums)==count*(H+1)
            rows.append({"H":H,"cutoff":t,"max_cost":max(sums),"profiles":len(sums)})
    return {"cases":tests,"rows":rows}


def mismatch():
    target=3; layers=[0,2]; H=0
    comparison=[u for u in layers if target<=1+u]
    small=[u for u in layers if u<=H]
    assert comparison and small and not set(comparison)&set(small)
    return {"target":target,"companions":layers,"comparison_witnesses":comparison,
            "cap_witnesses":small,"common_witnesses":[]}


def dyadic_budget():
    # At eps=1/64, x=2^(80k) gives log ceiling 2^k and t=2^(32080k).
    # ln(2)=2*sum_{j>=0}(1/3)^(2j+1)/(2j+1), positive terms.
    lower=Fraction(2,3)
    upper=lower+2*Fraction(1,3)**3/3/(1-Fraction(1,9))
    assert upper<Fraction(7,10)
    rows=[]
    for k in range(1,23):
        N=32080*k
        if N*upper<2**k: verdict="fits"
        elif (N-1)*lower>2**k: verdict="fails"
        else: raise ArithmeticError("Undecided with chosen log bounds")
        rows.append({"k":k,"log2_x":80*k,"target_log_ceiling":2**k,"cap_zero_budget":verdict})
    assert all(r["cap_zero_budget"]==("fails" if r["k"]<=18 else "fits") for r in rows)
    return {"companion_bound":0,"Ct":401,"eps":"1/64","ln2_lower":str(lower),
            "ln2_upper":str(upper),"tested":rows}


if __name__=="__main__":
    print(json.dumps(dict(costs=finite_costs(),quantifier_control=mismatch(),dyadic=dyadic_budget()),indent=2))
