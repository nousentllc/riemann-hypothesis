"""Exact inertia intersections in the abelian cyclotomic field of conductor 273."""
from itertools import product
from math import gcd
import json


def log_table(prime, generator):
    table = {pow(generator, exponent, prime): exponent for exponent in range(prime - 1)}
    if len(table) != prime - 1:
        raise ValueError("The specified element must generate every nonzero residue")
    return table


def evaluate():
    primes = (3, 7, 13)
    tables = [log_table(3, 2), log_table(7, 3), log_table(13, 2)]
    orders = (2, 3, 3)
    modulus = 273
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]

    def image(a):
        return tuple(table[a % p] % order for table, p, order in zip(tables, primes, orders))

    image_group = {image(a) for a in units}
    if image_group != set(product(range(2), range(3), range(3))):
        raise ValueError("Unexpected cyclotomic image")
    # Verify the representation on the whole unit group.
    for a, b in product(units, repeat=2):
        if image(a*b % modulus) != tuple((i+j) % n for i, j, n in zip(image(a), image(b), orders)):
            raise ValueError("Failed homomorphism identity")
    inertia = {p: {image(a) for a in units if a % (modulus // p) == 1} for p in primes}
    over_base = {g for g in image_group if g[0] == 0}
    cases = {}
    for label, (x, y) in {"diagonal_plus":(1,1), "diagonal_minus":(1,2), "coordinate":(1,0)}.items():
        over_middle = {g for g in over_base if (x*g[1]+y*g[2]) % 3 == 0}
        by_prime = {}
        for p in primes:
            in_base = inertia[p] & over_base
            in_middle = inertia[p] & over_middle
            by_prime[str(p)] = {"middle_over_base_e":len(in_base)//len(in_middle),
                                "top_over_middle_e":len(in_middle)}
        cases[label] = {"middle_over_base_degree":len(over_base)//len(over_middle),
                        "top_over_middle_degree":len(over_middle), "inertia":by_prime}
    zero = (0,0,0)
    assert image(modulus-1) == (1,0,0) and zero in over_base
    for name in ("diagonal_plus","diagonal_minus"):
        assert [cases[name]["inertia"][str(p)]["top_over_middle_e"] for p in primes] == [1,1,1]
        assert [cases[name]["inertia"][str(p)]["middle_over_base_e"] for p in primes] == [1,3,3]
    assert [cases["coordinate"]["inertia"][str(p)]["top_over_middle_e"] for p in primes] == [1,1,3]
    return {"modulus":modulus, "base":"Q(zeta_3)", "full_unit_count":len(units),
            "characters_image_order":len(image_group),
            "verified_products":len(units)**2, "complex_conjugation":image(modulus-1),
            "inertia_image_orders":{str(p):len(v) for p,v in inertia.items()}, "cases":cases}


if __name__ == "__main__":
    print(json.dumps(evaluate(),sort_keys=True,indent=2))
