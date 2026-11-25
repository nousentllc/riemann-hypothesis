"""Independent exact counting and Euler-factor controls for the six-square lattice."""
from collections import Counter
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

def primes(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n-p*p)//p + 1)
    return [p for p, flag in enumerate(sieve) if flag]

def factor(t):
    out = {}
    p = 2
    while p*p <= t:
        while t % p == 0:
            out[p] = out.get(p, 0) + 1
            t //= p
        p = 3 if p == 2 else p + 2
    if t > 1:
        out[t] = 1
    return out

def chi(a):
    return (0, 1, 0, -1)[a % 4]

def relative_factor(p, k):
    if p == 2:
        return (4 - F(1,16**k)) / 3
    x = F(chi(p), p*p)
    return sum((x**j for j in range(2*k+1)), F(0))

def ratio(t):
    out = F(1)
    for p,k in factor(t).items():
        out *= relative_factor(p,k)
    return out

def jacobi(n):
    count = 0
    for d in range(1,isqrt(n)+1):
        if n % d: continue
        e=n//d
        count += 16*chi(e)*d*d - 4*chi(d)*d*d
        if d != e:
            count += 16*chi(d)*e*e - 4*chi(e)*e*e
    return count

def integer_counts(n):
    hist=[1]+[0]*n
    for _ in range(6):
        child=hist.copy()
        for x in range(1,isqrt(n)+1):
            s=x*x
            for i in range(s,n+1):
                child[i]+=2*hist[i-s]
        hist=child
    return hist

def local_hist(q):
    squares=Counter(x*x%q for x in range(q))
    hist=[1]+[0]*(q-1)
    for _ in range(6):
        hist=[sum(m*hist[(y-z)%q] for z,m in squares.items()) for y in range(q)]
    assert sum(hist)==q**6
    return hist

def floor_interval(cut):
    ps = [p for p in primes(cut) if p%4==3]
    vals=[]
    for mode in (ROUND_FLOOR, ROUND_CEILING):
        with localcontext() as ctx:
            ctx.prec=30
            ctx.rounding=mode
            upper=Decimal(1)
            for p in ps:
                upper *= Decimal(p*p)/Decimal(1+p*p)
            # Sum_{n>cut} 1/n^2 <= 1/cut.  Product of (1-u_i) >= 1-sum u_i.
            vals.append(str(upper*(1-Decimal(1)/Decimal(cut))) if mode==ROUND_FLOOR else str(upper))
    return dict(cutoff=cut,inert_primes=len(ps),lower=vals[0],upper=vals[1])

def run():
    limit=64
    hist=integer_counts(limit**2)
    for n in range(1,len(hist)):
        assert hist[n]==jacobi(n)
    for t in range(1,limit+1):
        assert F(hist[t*t],12*t**4)==ratio(t)
    rows=[]
    for p in (3,5,7,11,13,17,19):
        for r in range(1,5):
            q=p**r
            if q>400:break
            h=local_hist(q)
            unit=F(1)-F(chi(p),p**3)
            for t in range(1,65):
                k=factor(t).get(p,0)
                if 2*k>=r:continue
                assert F(h[t*t%q],q**5)==unit*relative_factor(p,k)
            if r==1:
                assert h[0]==p**5+chi(p)*(p-1)*p**2
                assert all(h[a]==p**5-chi(p)*p**2 for a in range(1,p))
            rows.append(dict(p=p,r=r,modulus=q,regular_square_tests=sum(2*factor(t).get(p,0)<r for t in range(1,65))))
    minima_t=min(range(1,10001),key=ratio)
    ps=[3,7,11,19,23,31,43,47]
    approach=[]
    for j in (1,2,4,8):
        a=F(1)
        for p in ps[:j]:a*=relative_factor(p,j)
        approach.append(dict(primes=ps[:j],valuation=j,ratio=f'{float(a):.10f}'))
    return dict(integer_coefficients_checked=len(hist)-1,integer_square_targets=limit,
                odd_residue_histograms=rows,all_square_comparisons=sum(row['regular_square_tests'] for row in rows),
                samples=[dict(t=t,n=t*t,r6=jacobi(t*t),ratio=str(ratio(t))) for t in [1,2,3,4,5,7,9,21,27,63]],
                smallest_in_first_10000=dict(t=minima_t,ratio=str(ratio(minima_t)),decimal=float(ratio(minima_t))),
                floor_interval=floor_interval(100000),approach=approach)

if __name__=='__main__':
    payload=json.dumps(run(),indent=2)+'\n'
    out=Path(__file__).with_name('gaussian_product.json')
    if out.exists():
        assert out.read_text()==payload
    else:
        out.write_text(payload)
    print(payload)
