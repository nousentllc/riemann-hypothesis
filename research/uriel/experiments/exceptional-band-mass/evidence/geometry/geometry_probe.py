"""Exact experiments on logarithmic exception bands; standard-library only.

All geometric coordinates are Fractions. The ordinate in this file is the
logarithm of the original positive argument, in any common base.
"""
from fractions import Fraction as Q
from itertools import combinations
import json
from math import lcm

def hit_at(start, width, center, dilation):
    """Literal feasibility of a point in [start,width*start] and [a,B*a)."""
    left = max(start, center)
    return left <= width * start and left < dilation * center

def clean_oracle(lower, upper, width, centers, dilation):
    """A first clean candidate starts at lower or at a forbidden right edge."""
    for start in sorted({lower, upper, *(dilation * a for a in centers)}):
        if lower <= start <= upper and all(
            not hit_at(start, width, a, dilation) for a in centers
        ):
            return start
    return None

def interval_sweep(lower, upper, width, centers, dilation):
    """Independently merge half-open blocked intervals on possible starts."""
    if lower > upper:
        return None
    position = lower
    for a in sorted(centers):
        left, right = a / width, a * dilation
        if a <= 0 or dilation <= 1:
            continue
        if left <= position < right:
            position = right
    return position if position <= upper else None

def lower_adversary(width, dilation, count, ratio):
    """Cover [1,ratio] strictly; retry smaller rational relative slack."""
    product = width * dilation
    if count <= 0 or not (1 <= ratio < product**count and dilation > 1):
        raise ValueError("strict covering parameters required")
    slack = Q(1, 2)
    while ((1 - slack) * product) ** count <= ratio:
        slack /= 2
    first = (1 - slack) * width
    return [first * ((1 - slack) * product) ** j for j in range(count)]

def overlap(start, width, center, dilation):
    return max(Q(0), min(width*start, dilation*center) - max(start, center))

def share(start, width, center, dilation):
    return overlap(start, width, center, dilation) / ((width - 1) * start)

def one_band_formula(width, dilation, ratio):
    if dilation == 1:
        return Q(0)
    return max(Q(0), min(width-1, (dilation*width-ratio)/(dilation+ratio),
                         width*(dilation-1)/(ratio+dilation-1))) / (width-1)

def independent_optimum(width, dilation, ratio):
    """Piecewise affine optimization in center a, without the formula.

    For each of the two extreme starts the overlap as a function of center has
    kinks where an endpoint aligns. On a joint cell the lower of two affine
    functions is maximized at an endpoint or crossing.
    """
    knots = {Q(0)}
    for v in {Q(1), ratio}:
        knots.update([v, width*v, v/dilation, width*v/dilation])
    ordered = sorted(knots)
    candidates = set(knots)
    def diff(a):
        return share(Q(1),width,a,dilation) - share(ratio,width,a,dilation)
    for lo, hi in zip(ordered,ordered[1:]):
        d_lo, d_hi = diff(lo), diff(hi)
        if d_lo * d_hi < 0:
            candidates.add(lo - d_lo*(hi-lo)/(d_hi-d_lo))
    return max((min(share(Q(1),width,a,dilation),share(ratio,width,a,dilation)),a)
               for a in candidates)

def test_thresholds():
    dimensions = [Q(3,2),Q(2),Q(3)]
    dilations = [Q(1),Q(5,4),Q(3,2),Q(2),Q(3)]
    grid = list(map(Q, [-1,0,1,2,3,4,6,8,12,16])) + [Q(3,2)]
    totals = {"configurations":0, "clean":0, "fully_blocked":0,
              "at_or_above_threshold":0, "strict_adversaries":0}
    for w in dimensions:
        for b in dilations:
            for n in range(4):
                rcrit = (w*b)**n if b>1 else Q(1)
                for r in sorted({max(Q(1),rcrit*Q(3,4)),rcrit,rcrit*Q(5,4)}):
                    for centers in combinations(grid,n):
                        witness = clean_oracle(Q(1),r,w,centers,b)
                        swept = interval_sweep(Q(1),r,w,centers,b)
                        assert witness == swept
                        totals["configurations"] += 1
                        totals["clean" if witness is not None else "fully_blocked"] += 1
                        if r >= rcrit:
                            totals["at_or_above_threshold"] += 1
                            assert witness is not None
                    if b > 1 and 1 <= r < rcrit:
                        adversary = lower_adversary(w,b,n,r)
                        assert interval_sweep(Q(1),r,w,adversary,b) is None
                        assert all(adversary[i+1]/w < b*adversary[i] for i in range(n-1))
                        assert adversary[0]/w < 1 and b*adversary[-1] > r
                        totals["strict_adversaries"] += 1
    return totals

def main():
    totals = test_thresholds()
    ratios = list(map(Q, (1,2,3,4,6,8,12))) + [Q(5,4),Q(3,2),Q(5,2)]
    pairs = [(w,b) for w in (Q(3,2),Q(2),Q(3))
                 for b in (Q(1),Q(5,4),Q(3,2),Q(2),Q(3),Q(4))]
    checked = positive = intermediate = 0
    table = []
    for w,b in pairs:
        for r in sorted(ratios):
            direct, center = independent_optimum(w,b,r)
            formula = one_band_formula(w,b,r)
            assert direct == formula
            checked += 1
            positive += (formula>0)
            for i in range(17):
                v = 1 + (r-1)*i/16
                assert share(v,w,center,b) >= formula
                intermediate += 1
            if w==b==2:
                table.append({"r":str(r),"J":str(w*r),"fraction":str(formula),
                              "maximizing_center_over_min_start":str(center)})
    endpoint_cases = [
        ("only_right_endpoint_hits", Q(1),Q(2),Q(2),Q(2),True),
        ("excluded_right_edge_is_clean", Q(4),Q(2),Q(2),Q(2),False),
        ("empty_band", Q(1),Q(2),Q(2),Q(1),False)
    ]
    endpoints = []
    for name,v,w,a,b,expected in endpoint_cases:
        assert hit_at(v,w,a,b) == expected and overlap(v,w,a,b)==0
        endpoints.append({"case":name,"predicate_fails":expected,"area":"0"})
    integers = []
    for n in (1,2,3):
        w=b=Q(2)
        r=(w*b)**n-Q(1,2)
        aa = lower_adversary(w,b,n,r)
        scale = lcm(*[v.denominator for v in [r,*aa]])
        powers = [int(2*scale*a) for a in aa]
        assert all(Q(e,2)==scale*a for e,a in zip(powers,aa))
        assert clean_oracle(Q(scale),scale*r,w,[Q(e,2) for e in powers],b) is None
        integers.append({"R":n,"J":str(w*r),"sharp_J":str(w*(w*b)**n),
                         "base2_log_X":int(scale*w*r),"base2_log_min_start":scale,
                         "base2_log_integer_labels":powers})
    # In u=log2 x take [6,10] inside [6,12) forbidden by a=6, B=2.
    # Triangular pulse of u-width 4 and height 20, with zero exterior.
    def pulse_area(height):
        knots = [(Q(4),Q(0)),(Q(6),Q(0)),(Q(8),Q(height)),(Q(10),Q(0)),(Q(12),Q(0))]
        # All linear pieces have a constant sign. Clipping both values first
        # therefore integrates the positive part exactly on each piece.
        return sum((b-a)*(max(Q(0),ha)+max(Q(0),hb))/2
                   for (a,ha),(b,hb) in zip(knots, knots[1:]))
    assert pulse_area(20) == 40 and pulse_area(-20) == 0
    signal = {"width_in_u":4, "height":20,"positive_area_in_u":str(pulse_area(20)),
              "negative_pulse_positive_area":str(pulse_area(-20))}
    return {"rational_grid":totals,"one_band_formula_checks":checked,
            "positive_cases":positive,"intermediate_point_checks":intermediate,
            "one_band_lambda2_B2":table,"endpoint_controls":endpoints,
            "integer_label_constructions":integers,"triangle_control":signal}

if __name__=="__main__":
    print(json.dumps(main(),indent=2))
