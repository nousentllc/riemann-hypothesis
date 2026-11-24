"""Enumerate unit norm fibers in Z[i] modulo small odd prime powers."""
from collections import Counter
from fractions import Fraction
import json


def check(prime, power):
    modulus = prime**power
    squares = Counter(x*x % modulus for x in range(modulus))
    counts = Counter()
    for a, mult_a in squares.items():
        for b, mult_b in squares.items():
            counts[(a+b) % modulus] += mult_a*mult_b
    sign = 1 if prime % 4 == 1 else -1
    target = prime**(power-1)*(prime-sign)
    units = [t for t in range(modulus) if t % prime]
    if any(counts[t] != target for t in units) or sum(counts.values()) != modulus**2:
        raise ValueError(f"Norm counts disagree for {prime}^{power}")
    return dict(prime=prime,power=power,residue_modulus=modulus,
                splitting="split" if sign==1 else "inert",tested_unit_fibers=len(units),
                pairs_per_unit_fiber=target,density=str(Fraction(target,modulus)))


def main():
    rows = [check(p,k) for p in (3,5,7,11,13,17,19) for k in (1,2)]
    print(json.dumps(dict(field="Q(i)",form="x^2 + y^2",excluded_prime=2,
                          scope="Finite local arithmetic control at unramified primes; no global theta or Eisenstein value evaluated.",
                          unit_fibers=sum(r['tested_unit_fibers'] for r in rows),cases=rows),indent=2))


if __name__=='__main__':
    main()
