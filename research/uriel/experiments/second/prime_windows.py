"""Continuum maxima of Deduction.G(y)/sqrt(y) on four finite conductor-one windows."""
from math import isqrt
from functools import lru_cache
from mpmath import mp
from analytic import compare, serialize


def powers_from_sieve(limit):
    prime = bytearray([1])*(limit+1)
    prime[:2]=bytes(2)
    for p in range(2,isqrt(limit)+1):
        if prime[p]:
            prime[p*p::p]=bytes((limit-p*p)//p+1)
    out = {}
    for p in range(2,limit+1):
        if prime[p]:
            n = p
            while n<=limit:
                out[n]=p
                n *= p
    return out


@lru_cache(None)
def trial_prime_base(n):
    if n<2:
        return 0
    p = next((i for i in range(2,isqrt(n)+1) if n%i==0),n)
    while n%p==0:
        n //= p
    return p if n==1 else 0


def direct(y,omit=()):
    terms = (mp.log(p)*(y/n-1) for n in range(2,int(mp.floor(y))+1)
             if n not in omit and (p:=trial_prime_base(n)))
    return (mp.fsum(terms)-y*mp.log(y)+(1+mp.euler)*y)/mp.sqrt(y)


def window(Y,table):
    V = isqrt(Y**3)
    if V**2 != Y**3:
        raise ValueError("The specified grid uses integer endpoints")
    knots = [Y]+sorted(n for n in table if Y<n<V)+[V]
    A = 1+mp.euler+mp.fsum(mp.log(p)/n for n,p in table.items() if n<=Y)
    B = mp.fsum(mp.log(p) for n,p in table.items() if n<=Y)
    best,location = mp.ninf,None
    stationary = 0
    for left,right in zip(knots,knots[1:]):
        lo,hi = mp.mpf(left),mp.mpf(right)
        candidates = [lo,hi]
        def sign(y):
            return A-2-mp.log(y)+B/y
        if sign(lo)>0 and sign(hi)<0:
            # Bisection of a strictly decreasing derivative numerator on this smooth piece.
            for _ in range(mp.prec+8):
                mid = (lo+hi)/2
                if sign(mid)>0:
                    lo = mid
                else:
                    hi = mid
            candidates.append((lo+hi)/2)
            stationary += 1
        for y in candidates:
            value = (A*y-B-y*mp.log(y))/mp.sqrt(y)
            if value>best:
                best,location=value,y
        if right in table:
            logp = mp.log(table[right])
            A += logp/right
            B += logp
    endpoint = max(direct(mp.mpf(Y)),direct(mp.mpf(V)))
    full = direct(location)
    return dict(Y=Y,V=V,smooth_pieces=len(knots)-1,stationary_candidates=stationary,
                maximum=best,location=location,endpoints_only=endpoint,endpoint_shortfall=best-endpoint,
                direct_error=abs(best-full),omit_n4_delta=full-direct(location,(4,)),
                omit_n4_expected=mp.log(2)*(location/4-1)/mp.sqrt(location))


def measurements():
    table = powers_from_sieve(4096)
    rows = [window(y,table) for y in (4,16,64,256)]
    mid = mp.mpf("100.5")
    # Fixed continuous triangular bump in G/sqrt(y), supported on [100.25,100.75].
    bump = lambda y: 2*max(0,1-4*abs(y-mid))
    return dict(windows=rows,tables_agree=all(table.get(n,0)==trial_prime_base(n) for n in range(1,4097)),
                prime_powers=len(table),bump=dict(center=mid,center_perturbed=direct(mid)+bump(mid),
                unperturbed_window_max=rows[2]["maximum"],
                max_integer_change=max(bump(mp.mpf(n)) for n in range(64,513))))


def run():
    with mp.workdps(60):
        a=measurements()
    with mp.workdps(90):
        b=measurements()
        return serialize(dict(**b,precision_digits=[60,90],cross_precision_max=compare(a,b)))
