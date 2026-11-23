"""Exact implications of the redesigned principal rank budget; no assigned moving rank."""
import json
from fractions import Fraction

def panel():
    ct = 401
    tolerance = Fraction(1,64)
    ck = 1
    price = 4*ct*ck/tolerance
    assert price.denominator == 1
    rows = []
    for moving in (0,1,2):
        for fixed in (0,1,2):
            inherited = 4*price**(moving+fixed)
            redesigned = 4*price**moving
            assert inherited/redesigned == price**fixed
            assert redesigned == 2**(moving+2)*(2*ck*ct/tolerance)**moving
            rows.append(dict(assumed_moving=moving, assumed_old_odd_total=fixed,
                             inherited_J=str(inherited), redesigned_J=str(redesigned),
                             ratio=str(inherited/redesigned)))
    return dict(Ct=ct,epsilon=str(tolerance),assumed_CK=ck,cost_per_rank=str(price),rows=rows,
                interpretation="Illustrative parameters and matched even ranks. No rank of an existing witness was identified.")
if __name__=="__main__":
    print(json.dumps(panel(),indent=2))
