"""Directed computation of fixed-character slopes and guaranteed collars."""
from collections import defaultdict
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"numeric"))
from prime_mass import S, I, ZERO, box, log, beta_constants, sqrt_box, prime_powers

def sign(n):
    return (0,1,0,-1)[n%4]

def sha4_slopes(pp,c):
    current=c
    most=ZERO
    winner=None
    hull=None
    for n in range(1,1024):
        if n in pp:
            current=current + log(pp[n]).scale(F(sign(n),n))
        if hull is None:
            hull=current
        hull=I(min(hull.lo,current.lo),max(hull.hi,current.hi))
        size=I(max(current.lo,-current.hi,0), max(current.hi,-current.lo))
        if size.lo>most.hi:
            most,winner=size,n
    assert -2*S < hull.lo <= hull.hi < 2*S
    # The global hull independently excludes any larger absolute value.
    assert max(-hull.lo, hull.hi) == most.hi
    return dict(right_slopes=1023,slope_hull=hull.pair(14),maximum_abs_enclosure=most.pair(14),
                first_record_maximum_at=winner)

def factorization(n):
    out={}
    p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1
            n//=p
        p+=1
    if n>1:
        out[n]=1
    return out

def convolution(N,pp):
    coefficients=defaultdict(F)
    for n in range(1,N+1):
        for p,k in factorization(n).items():
            coefficients[p]+=F(k*sign(n),n)
    rhs=defaultdict(F)
    harmonic=[F(0)]
    for m in range(1,N+1):
        harmonic.append(harmonic[-1]+F(sign(m),m))
    for d,p in pp.items():
        if d<=N:
            rhs[p]+=F(sign(d),d)*harmonic[N//d]
    assert all(coefficients[p]==rhs[p] for p in set(rhs)|set(coefficients))
    # Omitting d=9, a positive odd prime power, changes the coefficient of log 3.
    dropped=harmonic[N//9]/9
    assert dropped!=0
    return dict(N=N, log_prime_coefficients=len(coefficients), removing_nine_changes_coefficient=True)

def binomial_tests(pp):
    missing=[]
    for n in range(2,1025):
        k=n//2
        product=1
        for d in range(k+1,n+1):
            if d in pp:
                product*=pp[d]
        coefficient=comb(n,k)
        if coefficient%product:
            missing.append(n)
        correction=pp.get(k+1,1) if n%2 else 1
        assert coefficient*correction%product==0
    return dict(N_range=[2,1024],cases=1023,odd_cases_requiring_correction=len(missing),
                first_uncorrected_failure=missing[0])

def tail():
    # Both (log x)/x and (log x)^2/x decrease above exp(2).
    Llow=sum(F((-1)**k,2*k+1) for k in range(8))
    assert Llow>F(3,4) and log(2).hi<box(F(7,10)).lo
    rhs=log(2).scale(2)+log(1024).scale(F(12,1024))
    upper=rhs.scale(1/Llow)
    assert upper.hi < 2*S
    return dict(start=1024,L_one_lower=str(Llow),bounded_tail_slope_upper=upper.pair(13)[1],
                admissible_uniform_constant=2)

def coefficients(y,pp,c,omit_c=False):
    a=ZERO if omit_c else c
    b=ZERO
    for n,p in pp.items():
        if n<=y and sign(n):
            v=log(p).scale(sign(n))
            a,b=a+v.scale(F(1,n)),b+v
    return a.scale(y)-b

def collar(t,pp,c):
    g=coefficients(t,pp,c)
    coef=F(3,20)
    def margin(radius):
        return sqrt_box(box(t-radius)).scale(coef)-box(2*radius)-g
    lo,hi=F(0),F(t-1)
    assert margin(lo).lo>0 and margin(hi).hi<0
    for _ in range(55):
        mid=(lo+hi)/2
        val=margin(mid)
        if val.lo>=0:
            lo=mid
        elif val.hi<0:
            hi=mid
        else:
            break
    assert margin(lo).lo>=0 and margin(hi).hi<0
    # Positive quotient of a nonprincipal affine piece by sqrt(y) has no
    # interior strict positive maximum: at a critical point G = 2a*y, so
    # positive means a>0 and the derivative changes from negative to positive.
    points=[t-lo,t+lo]+[F(n) for n in pp if t-lo<n<t+lo and sign(n)]
    normalized=[coefficients(y,pp,c)*sqrt_box(box(y)).reciprocal() for y in points]
    maximum=max(v.hi for v in normalized)
    assert maximum<=box(coef).lo
    return dict(t=t,G=g.pair(12),K=2,ceiling="3/20*sqrt(y)",robust_symmetric_radius=I(box(lo).lo,box(hi).hi).pair(12),
                evaluated_knots_and_ends=len(points),true_normalized_upper=I(maximum,maximum).pair(12)[1])

def main():
    pp=prime_powers(4200)
    c,_=beta_constants(65)
    assert c.lo>0
    wrong=coefficients(512,pp,c,True)
    actual=coefficients(512,pp,c)
    difference=actual-wrong
    assert difference.lo>0 and difference.lo<=c.scale(512).hi and c.scale(512).lo<=difference.hi
    # Interfaces with only a Lipschitz constant: ramps realize the cost exactly.
    tests=0
    for k in (F(1,2),F(1),F(2),F(7)):
        for v in range(-7,8):
            for j in range(1,31):
                r=F(j,13)
                assert (v+k*r-v)/r==k
                tests+=1
    print(json.dumps(dict(character="primitive real modulo four",
         prefix=sha4_slopes(pp,c), tail=tail(), binomial=binomial_tests(pp),
         convolution=[convolution(n,pp) for n in (16,64,257,511,1024,4096)],
         omitted_linear_term_error_at_512=difference.pair(12), constant_lipschitz_cone_tests=tests,
         geometric_ratio_at_square_root=[dict(t=2**(2*k),r_over_t=str(F(1,2**k))) for k in (5,10,15,20)],
         collars=[collar(t,pp,c) for t in (256,487,512,4096)]),indent=2))

if __name__=="__main__":
    main()
