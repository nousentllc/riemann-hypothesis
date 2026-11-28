"""Exact comparisons for exceptional-weight slack and an abstract bad-band counterexample."""
from fractions import Fraction as F
import json


def band_example():
    # Coordinates are u=log_2(x). For e=2^m, Good fails iff eta*u < m <= Ct*u.
    eps, ct = F(1,64), 401
    eta = eps/2
    rows = []
    for u in (64,128,256,512):
        m = u
        lo, hi = F(u), F(3,2)*u
        assert eta*hi < m <= ct*lo
        # A fixed normalized shape on each window, supported between
        # ratios 1 and 3/2 and equal to one on [5/4, 11/8].
        # On the plateau G(x)=x, theta=1/2. The lower bound uses
        # length in du times the smallest x^(1-theta) there.
        high = F(11,8)*u
        low = F(5,4)*u
        assert low < high
        rows.append({"log2_start":u,"log2_exception":m,"forbidden_log2_interval":[str(F(m,ct)),str(m/eta)],"entire_closed_window_bad":True,"plateau_log2_width":str(high-low),"log2_minimum_normalized_height":str(low/2)})
    return rows


def controls():
    eps, ck, u = F(1,64), F(1), 12800
    target = F(4,5)
    cases = []
    for channel, r, nominal in (("moving-coarse",F(1,4),F(11,20)),("odd-fixed",F(0),F(4,5))):
        for a in (nominal-F(1,40), nominal, nominal+F(1,40)):
            s = r+a
            # Set log_2 x = 12800. The ratio of the raw and target
            # log-envelopes is A * 2**((s-target)*eps*u), hence integral powers here.
            power = (s-target)*eps*u
            assert power.denominator==1
            ratios=[A*F(2)**int(power) for A in (F(1,2),F(1),F(2))]
            cases.append({"channel":channel,"a":str(a),"r":str(r),"raw_exponent_in_epsilon_units":str(s),"strict_asymptotic_margin":s<target,"ratio_log_envelopes_at_log2x_12800":[str(v) for v in ratios]})
            assert s<target or ratios[-1]>1
            if s==target: assert ratios == [F(1,2),F(1),F(2)]
    # At a genuine (integer) Ct cutoff, inactive upper-bound exception.
    t=256**2
    exceptional=t
    assert 256 < exceptional <= t
    assert all(1<=k<exceptional for k in range(1,t))
    # Compare retained positive budgets with an exact lower bound for the
    # consumed polynomial overhead when a=t and A>=1.
    assert target-F(1,4)==F(11,20) and target-F(1,5)==F(3,5)
    assert (F(3,5)-F(1,100))+(F(1,5)+F(1,200)) < target
    return {
        "slack":cases,
        "active_cutoff":{"x":256,"Ct":2,"eta":1,"exception":exceptional,"t":t,"original_good":False,"active_bad_indices":0,"finite_enumeration_size":t-1},
        "actual_pair_refinement_exponents":{"a":str(F(59,100)),"r_after_log_absorption":str(F(41,200)),"sum":str(F(159,200)),"target":str(target)},
        "countermodel":band_example(),
        "scope":"Finite exact controls of inequalities. Multiplicative constants are independently chosen adversarial inputs; countermodel signals are neither Dirichlet characters nor outputs of upstream cohomology."
    }


if __name__=="__main__":
    print(json.dumps(controls(),indent=2))
