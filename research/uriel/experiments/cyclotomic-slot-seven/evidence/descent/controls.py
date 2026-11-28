"""Finite controls for generation by seventh powers and lengths of twisted cokernels."""
from itertools import product
from math import gcd, prod
import json


def seventh_power_quotient(factors):
    """Return the entire domain order and its quotient order by the seventh powers."""
    domain = list(product(*(range(d) for d in factors)))
    image = {tuple(7 * x % d for x, d in zip(v, factors)) for v in domain}
    quotient, rem = divmod(len(domain), len(image))
    assert not rem
    assert quotient == prod(gcd(7, d) for d in factors)
    assert (quotient == 1) == (len(domain) % 7 != 0)
    return {"factors":list(factors), "order":len(domain), "image":len(image), "quotient":quotient}


def cokernel(unit, exponent, m, modulus):
    """Check the module size by an exact image count and an independent gcd."""
    if modulus == 1:
        # The trivial ring/module model has one element and one endomorphism.
        coefficient = 0
    else:
        coefficient = (pow(unit, exponent * 7**m, modulus) - 1) % modulus
    image = {coefficient * i % modulus for i in range(modulus)}
    order = modulus // len(image)
    assert order == gcd(coefficient, modulus)
    length = 0
    rest = order
    while rest % 7 == 0:
        length += 1
        rest //= 7
    assert rest == 1
    return length


def run():
    prime = 7
    groups = [(), (2,), (3,), (2,3), (5,6), (8,9), (7,), (14,), (49,), (7,7), (49,7)]
    rows = [seventh_power_quotient(f) for f in groups]
    assert rows[5]["order"] == 72 and rows[5]["quotient"] == 1
    assert rows[-1]["quotient"] == 49
    signed = [-7,-6,-1,1,6,7]
    matrices = []
    for modulus in (1,49):
        for u in (2,8):
            for j in signed:
                lengths=[cokernel(u,j,m,modulus) for m in range(3)]
                assert lengths==[cokernel(u,-j,m,modulus) for m in range(3)]
                if modulus==1:
                    assert lengths==[0,0,0]
                matrices.append({"modulus":modulus,"u":u,"j":j,"lengths":lengths})
    assert [cokernel(8,1,m,49) for m in range(3)] == [1,2,2]
    assert [cokernel(2,1,m,49) for m in range(3)] == [0,0,0]
    assert [cokernel(2,6,m,49) for m in range(3)] == [1,2,2]
    zero_budget = [(m,b) for m in (0,1,2,3,4,10,10**6) for b in (0,1,25,10**6)]
    assert prime**0 == 1 and all(0 * (max(m,3) + 0 + b) == 0 for m,b in zero_budget)
    return {"prime":prime,"power_quotients":rows,"cokernel_cells":3*len(matrices),
            "degree_list":[0,1,2],"cokernels":matrices,"empty_center_budget_cells":len(zero_budget),
            "interpretation":"Finite algebraic controls. No computed cell samples an arithmetic Sha group."}

if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
