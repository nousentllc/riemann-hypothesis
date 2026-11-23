"""Finite controls for the served inert prime study. Requires Python 3.9 or later."""
import argparse
from bisect import bisect_left, bisect_right
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import fsum, isqrt, log
from pathlib import Path


CUTS = (1000, 10000, 100000, 1000000)
WINDOW = (7, 11, 13, 17, 19, 23, 29, 31)
INITIAL_CAP = 500000
SEARCH_CAP = 5000000


def prime_list(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b"\0\0"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = b"\0" * ((limit - p*p)//p + 1)
    return [p for p in range(2, limit+1) if flags[p]]


def symbol(a, odd_prime):
    v = pow(a % odd_prime, (odd_prime - 1)//2, odd_prime)
    return -1 if v == odd_prime - 1 else v


def discr_at(p, modulus):
    if p == 2:
        return 1 if -modulus % 8 in (1, 7) else -1
    return symbol(-modulus, p)


def find_controls(primes):
    pool = primes[bisect_right(primes, 32):bisect_right(primes, SEARCH_CAP)]
    q = next(q for q in pool if q % 8 == 3 and
             all(discr_at(p, q) == -1 for p in WINDOW))
    ds = []
    for sign in (1, -1):
        d = next(d for d in pool if d % 16 == 7 and discr_at(q, d) == 1
                 and all(discr_at(p, d) == 1 for p in (3, 5))
                 and all(discr_at(p, d) == sign for p in WINDOW))
        ds.append(d)
    return q, ds


def class_and_weights(q, d, primes, limit):
    # Compare reciprocity against Euler's test via precomputed square residues.
    def square_residues(modulus):
        result = bytearray(modulus)
        for a in range(1, (modulus+1)//2):
            result[a*a % modulus] = 1
        return result
    qr, dr = square_residues(q), square_residues(d)
    inert, atoms = [], []
    for p in primes:
        first, second = discr_at(p, q), discr_at(p, d)
        independent_q = 0 if p % q == 0 else (1 if qr[p % q] else -1)
        independent_d = 0 if p % d == 0 else (1 if dr[p % d] else -1)
        assert (first, second) == (independent_q, independent_d)
        is_inert = p not in (2,q,d) and first == second == -1
        if is_inert:
            inert.append(p)
        pe, exponent = p, 1
        while pe <= limit:
            u, v = first**exponent, second**exponent
            numerator = 1-u-v+u*v
            assert numerator == (1-u)*(1-v) and 0 <= numerator <= 4
            if exponent == 1 and p not in (2,q,d):
                assert (numerator == 4) == is_inert
            if numerator:
                atoms.append((pe, numerator * log(p)/4))
            exponent += 1
            pe *= p
    atoms.sort()
    return inert, atoms


def evaluate_pair(q, d, primes):
    limit = 5*CUTS[-1]//4
    inert, atoms = class_and_weights(q,d,primes,limit)
    positions = [n for n, _ in atoms]
    rows = []
    for H in CUTS:
        support = inert[:bisect_left(inert,H)]
        raw = fsum(log(p) for p in support)
        upto = bisect_left(positions,H)
        cumulative = fsum(w for _,w in atoms[:upto])
        brackets = []
        def F(t):
            return fsum(w*float((t-n)/n) for n,w in atoms[:bisect_left(positions,t)])
        value = F(float(H))
        for divisor in (4,16,64):
            width = H/divisor
            lower = (value-F(H-width))/width-value/H
            upper = (F(H+width)-value)/width-value/H
            assert lower-2e-10 <= cumulative/H <= upper+2e-10
            brackets.append([divisor, round(lower,10), round(upper,10)])
        assert 0 <= cumulative-raw <= (isqrt(H)*log(H)+log(2*q*d)) + 2e-9
        rows.append({"H":H,"prime_count":len(support),"theta_over_H":round(raw/H,10),
                     "projected_psi_over_H":round(cumulative/H,10),
                     "prime_list_sha256":sha256(",".join(map(str,support)).encode()).hexdigest(),
                     "secants":[{"reciprocal_relative_width":v,"low":l,"high":u} for v,l,u in brackets]})
    return {"q":q,"d":d,"window_support":[p for p in WINDOW if p in inert],"cutoffs":rows}


def exact_controls():
    fs = Fraction
    positions = (2,4,5,6,7)
    H, width = 5,2
    cases = 0
    for weights in product((0,1,2),repeat=len(positions)):
        for slope in (-3,0,9):
            def A(t):
                return sum(w*max(fs(t,n)-1,0) for n,w in zip(positions,weights)) + slope*t
            low = H*(A(H)-A(H-width))/width-A(H)
            high = H*(A(H+width)-A(H))/width-A(H)
            strict = sum(w for n,w in zip(positions,weights) if n<H)
            inclusive = sum(w for n,w in zip(positions,weights) if n<=H)
            assert low <= strict <= inclusive <= high
            cases += 1
    # Remove positivity with one negative atom to either side or at the cut.
    signed = []
    for n in (4,5,6):
        def negative(t):
            return -max(fs(t,n)-1,fs(0))
        lower = H*(negative(H)-negative(H-width))/width-negative(H)
        upper = H*(negative(H+width)-negative(H))/width-negative(H)
        strict, inclusive = -int(n < H), -int(n <= H)
        assert not (lower <= strict <= inclusive <= upper)
        signed.append({"position":n,"lower":str(lower),"strict":strict,
                       "inclusive":inclusive,"upper":str(upper)})
    return {"exact_secant_cases":cases,"signed_controls":signed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",type=Path,help="compare counts, fingerprints and printed values")
    args = parser.parse_args()
    pool = prime_list(SEARCH_CAP)
    q, ds = find_controls(pool)
    primes = pool[:bisect_right(pool,5*CUTS[-1]//4)]
    out = {"initial_search_cap":INITIAL_CAP,"final_search_cap":SEARCH_CAP,
           "first_found_within_initial_cap":[d <= INITIAL_CAP for d in ds],
           "exact_controls":exact_controls(),
           "pairs":[evaluate_pair(q,d,primes) for d in ds]}
    assert not out["pairs"][0]["window_support"]
    assert tuple(out["pairs"][1]["window_support"]) == WINDOW
    if args.check:
        if out != json.loads(args.check.read_text()):
            raise SystemExit("Recorded output differs")
        print("Finite arithmetic and secant results reproduced.")
    else:
        print(json.dumps(out,indent=2))


if __name__ == "__main__":
    main()
