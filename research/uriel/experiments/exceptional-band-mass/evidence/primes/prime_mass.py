"""Continuous finite-window enclosures for the unit and real mod-four characters.

Python standard library only. Usage: python3 -B prime_mass.py > results.json
All comparisons and printed interval endpoints use outward integer/rational arithmetic.
"""
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import comb, isqrt
from pathlib import Path

S = 2**160
LOG_TERMS = 55


def ceil(a, b):
    return -((-a) // b)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __add__(self, other):
        return I(self.lo+other.lo, self.hi+other.hi)

    def __sub__(self, other):
        return I(self.lo-other.hi, self.hi-other.lo)

    def scale(self, rational):
        f = F(rational)
        a,b=sorted((self.lo*f.numerator,self.hi*f.numerator))
        return I(a//f.denominator,ceil(b,f.denominator))

    def __mul__(self, other):
        a = [v*w for v in (self.lo,self.hi) for w in (other.lo,other.hi)]
        return I(min(a)//S,ceil(max(a),S))

    def reciprocal(self):
        assert self.lo>0
        return I(S*S//self.hi,ceil(S*S,self.lo))

    def pair(self, digits=12):
        base=10**digits
        def string(x):
            prefix='-' if x<0 else ''
            a,b=divmod(abs(x),base)
            return f'{prefix}{a}.{b:0{digits}d}'
        return [string(self.lo*base//S),string(ceil(self.hi*base,S))]


def box(rational):
    f=F(rational)*S
    return I(f.numerator//f.denominator,ceil(f.numerator,f.denominator))


ZERO=box(0)
ONE=box(1)


def log_unit(q):
    z=(q-1)/(q+1)
    assert F(0)<=z<=F(1,3)
    a=z.numerator*S//z.denominator
    b=ceil(z.numerator*S,z.denominator)
    aa=a*a//S
    bb=ceil(b*b,S)
    l=h=0
    for k in range(1,2*LOG_TERMS,2):
        l+=2*a//k; h+=ceil(2*b,k)
        a=a*aa//S; b=ceil(b*bb,S)
    k=2*LOG_TERMS+1
    return I(l,h+ceil(9*S,4*k*3**k))


LOG2=log_unit(F(2))


@lru_cache(maxsize=131072)
def log(q):
    q=F(q)
    k=q.numerator.bit_length()-q.denominator.bit_length()
    u=q/F(2)**k
    if u<1:
        k-=1;u*=2
    return log_unit(u)+LOG2.scale(k)


def sqrt_box(a):
    low=isqrt(a.lo*S); high=isqrt(a.hi*S)
    return I(low,high+(high*high<a.hi*S))


@lru_cache(maxsize=131072)
def pow_theta(y, quarter):
    root=sqrt_box(box(y))
    if quarter==2:return root
    assert quarter==3
    return root*sqrt_box(root)


def euler_gamma():
    n=10**6
    total=sum(S//k for k in range(1,n+1))
    correction=I(box(F(1,2*(n+1))).lo,box(F(1,2*n)+F(1,2*n*n)).hi)
    return I(total,total+n)-log(n)-correction


def beta_constants(terms=55,direct=8192):
    """Euler transform and independent adjacent alternating partial sums."""
    den=num=ZERO
    for j in range(terms):
        w=2**(j+1)
        for r in range(j+1):
            n=2*r+1
            coeff=F((-1)**r*comb(j,r),w*n)
            den=den+box(coeff)
            num=num+log(n).scale(-coeff)
    den=den+I(0,box(F(1,2**terms)).hi)
    tail=box(F(3,2**terms)).hi
    num=num+I(-tail,tail)
    a=b=ZERO
    for r in range(direct):
        n=2*r+1
        coeff=F((-1)**r,n)
        a=a+box(coeff)
        b=b+log(n).scale(-coeff)
    next_n=2*direct+1
    aa=a+box(F((-1)**direct,next_n))
    bb=b+log(next_n).scale(F(-(-1)**direct,next_n))
    slow=I(min(b.lo,bb.lo),max(b.hi,bb.hi))*I(min(a.lo,aa.lo),max(a.hi,aa.hi)).reciprocal()
    fast=num*den.reciprocal()
    assert slow.lo<fast.lo<=fast.hi<slow.hi
    return fast,dict(terms=terms,direct_terms=direct,L=den.pair(17),L_prime=num.pair(17),
                     ratio=fast.pair(16),ordinary_ratio=slow.pair(9))


def prime_powers(limit):
    sieve=bytearray([1])*(limit+1)
    sieve[:2]=b'\0\0'
    for n in range(2,isqrt(limit)+1):
        if sieve[n]:
            sieve[n*n::n]=bytes((limit-n*n)//n+1)
    pp={}
    for p in range(2,limit+1):
        if sieve[p]:
            n=p
            while n<=limit:
                pp[n]=p;n*=p
    def trial(n):
        q=next((j for j in range(2,isqrt(n)+1) if n%j==0),n)
        while n%q==0:n//=q
        return q if n==1 else None
    assert all(pp.get(n)==trial(n) for n in range(2,limit+1))
    return pp


def triangular_area(left,right):
    """Positive-part mean of the chord interpolating two rational ordinates."""
    if min(left,right)>=0:return F(left+right,2)
    if max(left,right)<=0:return F(0)
    top=max(left,right)
    return F(top*top,2*abs(left-right))


def build_segments(Y,principal,c4,gamma,pp):
    end=Y*isqrt(Y)
    knots=[Y]+[n for n in sorted(pp) if Y<n<end]+[end]
    a=ONE+gamma if principal else c4
    b=ZERO
    def term(n):
        p=pp[n]
        sign=1 if principal else (0,1,0,-1)[n%4]
        v=log(p).scale(sign)
        return v.scale(F(1,n)),v
    for n in pp:
        if n<=Y:
            v,z=term(n);a=a+v;b=b+z
    for left,right in zip(knots,knots[1:]):
        yield left,right,a,b
        if right in pp:
            v,z=term(right);a=a+v;b=b+z


def enclose(Y,principal,c4,gamma,pp,resolution=2048):
    theta_quarters=(2,3)
    state={j:dict(mass=ZERO,peak=None,endpoints=None,witness=None) for j in theta_quarters}
    cells=0; positivity=[0,0,0]
    for left,right,a,b in build_segments(Y,principal,c4,gamma,pp):
        count=max(1,ceil(resolution*(right-left),left))
        h=F(right-left,count)
        def val(y):
            return (a-log(y)).scale(y)-b if principal else a.scale(y)-b
        x=F(left);v=val(x)
        for i in range(count):
            y=x+h;w=val(y)
            curvature=box(h*h/(8*x)).hi if principal else 0
            area_lo=triangular_area(v.lo,w.lo)*h/S
            area_hi=triangular_area(v.hi+curvature,w.hi+curvature)*h/S
            if min(v.lo,w.lo)>0:positivity[0]+=1
            elif max(v.hi,w.hi)+curvature<=0:positivity[1]+=1
            else:positivity[2]+=1
            for j in theta_quarters:
                stats=state[j]
                xl=pow_theta(x,j);yr=pow_theta(y,j)
                ordinates=(v*xl.reciprocal(),w*yr.reciprocal())
                max_g=max(v.hi,w.hi)+curvature
                peak_hi=(I(max_g,max_g)*(xl if max_g>=0 else yr).reciprocal()).hi
                sampled=max(ordinates[0].lo,ordinates[1].lo)
                hiarg=(x if ordinates[0].lo>=ordinates[1].lo else y)
                current=stats['peak']
                if current is None or sampled>current.lo:stats['witness']=str(hiarg)
                stats['peak']=I(sampled,peak_hi) if current is None else I(max(sampled,current.lo),max(peak_hi,current.hi))
                if x==Y:stats['endpoints']=ordinates[0]
                if y==Y*isqrt(Y):
                    old=stats['endpoints']
                    stats['endpoints']=I(max(old.lo,ordinates[1].lo),max(old.hi,ordinates[1].hi))
                mass_lo=yr.reciprocal().scale(area_lo/y).lo
                mass_hi=xl.reciprocal().scale(area_hi/x).hi
                stats['mass']=stats['mass']+I(mass_lo,mass_hi)
            x=y;v=w;cells+=1
    width=log(F(isqrt(Y)))
    rows=[]
    for j,s in state.items():
        peak=s['peak'];mass=s['mass'];endpoints=s['endpoints']
        cap=I(max(0,peak.lo),max(0,peak.hi))*width
        ratio=(mass*cap.reciprocal()).pair(8) if cap.lo>0 else None
        assert mass.lo>=0 and mass.lo<=cap.hi
        rows.append(dict(Y=Y,end=Y*isqrt(Y),theta=str(F(j,4)),character='1' if principal else 'chi4',
                         peak=peak.pair(8),mass=mass.pair(8),peak_logwidth=cap.pair(8),ratio=ratio,
                         endpoint_peak=endpoints.pair(8),peak_lower_witness=s['witness'],
                         mass_width_below_four_per_mille=mass.hi==0 or (mass.lo>0 and (mass.hi-mass.lo)*250<mass.lo),
                         cells=cells,sign_cells=positivity))
    return rows


def run():
    spec=json.loads(Path(__file__).with_name('protocol.json').read_text())
    pp=prime_powers(4096);c4,beta=beta_constants();gamma=euler_gamma()
    rows=[]
    for principal in (True,False):
        for y in spec['Y']:rows.extend(enclose(y,principal,c4,gamma,pp))
    def bounds(row,key):return list(map(F,row[key]))
    old=next(r for r in rows if (r['Y'],r['theta'],r['character'])==(256,'1/2','1'))
    pl,pu=bounds(old,'peak')
    assert pl<=F('.1177870108') and pu>=F('.1177870105')
    # With no logarithmic-width factor, a saturated unit envelope would
    # incorrectly bound its integral by 1 on this interval.
    assert log(16).lo>S
    sign=next(r for r in rows if (r['Y'],r['theta'],r['character'])==(256,'1/2','chi4'))
    # On the entire last window a sign flip changes H_theta by -2c y^(1-theta).
    mutated_upper=box(bounds(sign,'peak')[1])-c4.scale(2*isqrt(256))
    assert c4.lo>0 and mutated_upper.hi<0
    return dict(protocol_sha256=hashlib.sha256(Path(__file__).with_name('protocol.json').read_bytes()).hexdigest(),
                fixedpoint_bits=160,log_terms=LOG_TERMS,relative_mesh=2048,prime_powers=len(pp),
                constants=dict(gamma=gamma.pair(13),beta=beta),rows=rows,
                controls=dict(overlaps_prior_peak=True,without_logwidth_saturator_mass=log(16).pair(8),
                    wrong_sign_chi4_peak_upper=mutated_upper.pair(8)[1],
                    strict_endpoint_misses=sum(bounds(r,'endpoint_peak')[1]<bounds(r,'peak')[0] for r in rows),
                    mass_certified_below_full_peak_allowance=sum(bounds(r,'mass')[1]<=bounds(r,'peak_logwidth')[0] for r in rows),
                    ratio_below_95pct=sum(r['ratio'] is not None and F(r['ratio'][1])<F(95,100) for r in rows),
                    relative_accuracy_passes=sum(r['mass_width_below_four_per_mille'] for r in rows)))


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
