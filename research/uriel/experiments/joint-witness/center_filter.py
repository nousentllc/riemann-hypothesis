"""Evaluate the finite near-set with supplied rational p-adic centers and exact controls."""
from fractions import Fraction
import json
from math import gcd

SLOTS = {
    2: (1, 129, 64, 65, Fraction(1,3)),
    3: (1, 28, 64, 80, Fraction(1,2)),
    7: (7, 56, 64, 65, Fraction(1,2)),
}


def floor_log(p, z):
    if p < 2 or z < 1:
        raise ValueError("Expected p >= 2 and positive Z")
    h = 0
    while p**(h+1) <= z:
        h += 1
    return h


def from_residue(p, z, center, strict=True):
    """Solve the normalized p-adic inequality by positive residue representatives."""
    center = Fraction(center)
    if gcd(p, center.denominator) != 1:
        raise ValueError("This residue model requires a rational p-adic integer")
    h = floor_log(p,z)
    modulus = p**(h+int(strict))
    residue = center.numerator * pow(center.denominator, -1, modulus) % modulus
    return list(range(residue or modulus, z+1, modulus))


def enumerate_norm(p, z, center, strict=True):
    """Literal filter. Compute each valuation by repeated division."""
    center = Fraction(center)
    if center.denominator % p == 0:
        raise ValueError("Denominator is outside the fixture domain")
    threshold = Fraction(1,p**floor_log(p,z))
    hits = []
    for e in range(1,z+1):
        numerator = abs(center.numerator-e*center.denominator)
        norm = Fraction(0)
        if numerator:
            order = 0
            while numerator % p == 0:
                order += 1
                numerator //= p
            norm = Fraction(1,p**order)
        accepted = norm < threshold if strict else norm <= threshold
        if accepted:
            hits.append(e)
    return hits


def whole_window(union, y):
    """Ct=1, eta=1/128. For e>0 the forbidden interval is [e,e^128)."""
    for e in sorted(union):
        first = max(y,e)
        if first <= y*y and first < e**128:
            return {"exception":e, "point":first}
    return None


def experiment():
    z = 64
    by_slot = []
    union = set()
    for p,centers in SLOTS.items():
        h = floor_log(p,z)
        component = set()
        checks = []
        for c in centers:
            hits = from_residue(p,z,c)
            weak = from_residue(p,z,c,False)
            if hits != enumerate_norm(p,z,c) or weak != enumerate_norm(p,z,c,False):
                raise AssertionError((p,z,c))
            component.update(hits)
            checks.append({"center":str(c), "strict":hits,"weak":weak})
        by_slot.append({"p":p,"h":h,"strict_modulus":p**(h+1),"centers":checks,
                        "exceptional":sorted(component)})
        union.update(component)
    # Regression at and around exact p-powers, including h=0 and the positive endpoint.
    trials = 0
    for p in SLOTS:
        for ztest in sorted({max(1,p**h+delta) for h in (0,1,2,3) for delta in (-1,0,1)}):
            for c in (Fraction(-1), Fraction(0), Fraction(1), Fraction(ztest), Fraction(ztest+1),
                      Fraction(1,p+1), Fraction(2,p+1)):
                for strict in (False,True):
                    hits = from_residue(p,ztest,c,strict)
                    if hits != enumerate_norm(p,ztest,c,strict) or (strict and len(hits)>1):
                        raise AssertionError((p,ztest,c,strict))
                    trials += 1
    R = sum(map(len,SLOTS.values()))
    J = 2**(R+2)*128**R
    success, failure = whole_window(union,2),whole_window(union,8)
    # X=2^6 and Y=2, so X^(1/J)<=Y is equivalent to 6<=J.
    if success is not None or failure != {"exception":7,"point":8} or J<6 or 2**2>z:
        raise AssertionError("Whole-window or range control failed")
    if by_slot[0]["exceptional"] != [1,43,64] or 64 not in union:
        raise AssertionError("Endpoint or rational center check failed")
    if from_residue(7,z,7) != [7] or from_residue(7,z,7,False) != [7,56]:
        raise AssertionError("Equality control did not distinguish the two inequalities")
    return {"scope":"post-registration fixture, supplied rational p-adic centers",
            "Z":z,"components":by_slot,"union":sorted(union),"input_centers":R,
            "union_cardinality":len(union),"control_enumerations":trials,
            "window":{"X":64,"Ct":1,"eta":"1/128","J":str(J),"Y":2,
                      "covered":[2,4],"good":success is None,
                      "candidate_Y":8,"candidate_interval":[8,64],"counterexample":failure}}


if __name__ == "__main__":
    print(json.dumps(experiment(),indent=2,sort_keys=True))
