"""Finite, prime-certified tests of two canonical row schedules. Python 3.11+, standard library."""
from dataclasses import dataclass
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as F
from math import gcd, isqrt
import json

PRECISION = 815


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def scale(self, number):
        assert number >= 0
        return Interval(self.lo * number, self.hi * number)

    def floor(self):
        left, right = int(self.lo // 1), int(self.hi // 1)
        assert left == right
        return left

    def exp(self):
        return elementary("exp",self)


def exact(value):
    return Interval(F(value),F(value))


def elementary(operation, x):
    """Bracket a monotone Decimal elementary evaluation including input conversion."""
    with localcontext() as ctx:
        ctx.prec = PRECISION
        result=[]
        for bound, rounding in ((x.lo,ROUND_FLOOR),(x.hi,ROUND_CEILING)):
            ctx.rounding=rounding
            val=Decimal(bound.numerator)/Decimal(bound.denominator)
            ans=getattr(val,operation)()
            result.append(F(ans.next_minus() if rounding == ROUND_FLOOR else ans.next_plus()))
    return Interval(*result)


def strict(a,b):
    if a.hi<b.lo:
        return True
    if b.hi<=a.lo:
        return False
    raise ArithmeticError("unresolved strict comparison")


def show(a,places=10):
    grid=10**places
    def endpoint(value,high):
        i=-((-value*grid)//1) if high else (value*grid)//1
        return f"{i//grid}.{i%grid:0{places}d}"
    return [endpoint(a.lo,False),endpoint(a.hi,True)]


def prime_certificate(bits=1400):
    """Find n with a fully certified large prime factor of n-1 recursively."""
    base=1031
    small=[k for k in range(2,600) if all(k % j for j in range(2,isqrt(k)+1))]
    chain=[]
    r=base
    while r.bit_length()<bits:
        width=min(bits,2*r.bit_length()-2)
        t=((1<<(width-1))+2*r-2)//(2*r)
        final=width==bits
        while True:
            n=2*r*t+1
            assert n<r*r and n.bit_length()==width
            if (not final or (n%16==7 and n%3==2)) and all(n%p for p in small):
                for a in (2,3,5,7,11,13,17):
                    if pow(a,n-1,n)!=1:
                        break
                    if gcd(pow(a,(n-1)//r,n)-1,n)==1:
                        break
                else:
                    t+=1
                    continue
                if pow(a,n-1,n)==1 and gcd(pow(a,(n-1)//r,n)-1,n)==1:
                    break
            t+=1
        chain.append(dict(n=str(n),factor=str(r),multiplier=str(2*t),base=a))
        r=n
    return dict(trial_prime=base,chain=chain)


def check_certificate(certificate):
    r=certificate["trial_prime"]
    assert r>=2 and all(r%j for j in range(2,isqrt(r)+1))
    for row in certificate["chain"]:
        n,k,a=int(row["n"]),int(row["multiplier"]),row["base"]
        assert r==int(row["factor"]) and n==k*r+1 and r*r>n
        assert pow(a,n-1,n)==1 and gcd(pow(a,k,n)-1,n)==1
        r=n
    return r


def bands(log_y):
    z=exact(log_y/360).exp()
    return z,z.scale(log_y**2)


def test():
    certificate=prime_certificate()
    d=check_certificate(certificate)
    log_d=elementary("ln",exact(d))
    q=3
    log_q=elementary("ln",exact(q))
    half=F(1,2)
    log2=elementary("ln",exact(2))
    a,b=F(72),F(76)  # log coordinates of the prespecified target
    Y=F(36)
    z,h=bands(Y)
    rows=[]
    for name,V in (("baseline",Y),("tiny",Y+F(1,10**320)),("moderate",Y+F(1,10000)),("separated",F(50))):
        altz,alth=bands(V)
        gq=strict(altz.scale(half).exp(),exact(z.scale(half).exp().floor()+1))
        gd=strict(alth.scale(half).exp(),exact(h.scale(half).exp().floor()+1))
        gz=strict(altz,exact(z.floor()+1))
        upper=strict(altz-z+alth-h,log2)
        domain=V<=a<=b<=4*V
        primes=[p for p in range(3,altz.floor()+1,2) if all(p%v for v in range(2,isqrt(p)+1))]
        assert domain and d%16==7 and d%q==q-1 and all((d+1)%p==0 for p in primes)
        q_ok=strict(altz.scale(half),log_q) and strict(log_q,altz)
        d_ok=strict(alth.scale(half),log_d) and strict(log_d,alth)
        rows.append(dict(version=name,log_Y=f"{V.numerator}/{V.denominator}",z=show(altz),h=show(alth),
                         whole_fixed_target_in_query=domain,integer_q_guard=gq,integer_d_guard=gd,small_prime_guard=gz,
                         doubled_height_guard=upper,horizon_guard=4*V<5*Y,
                         q_band=q_ok,d_band=d_ok,odd_small_primes=primes,
                         strict_q_separation=not strict(altz,z.scale(2)),strict_d_separation=not strict(alth,h.scale(2))))
    assert [row["d_band"] for row in rows]==[True,True,True,False]
    assert all(row["q_band"] for row in rows)
    assert all(rows[1][n] for n in ("integer_q_guard","integer_d_guard","small_prime_guard","doubled_height_guard","horizon_guard"))
    assert not rows[2]["integer_d_guard"] and rows[2]["d_band"]
    assert rows[3]["strict_d_separation"] and not rows[3]["strict_q_separation"]
    counts=dict(overlap=0,equality_q=0,q_disjoint=0,d_disjoint=0)
    for u in range(1,13):
        for v in range(u,13):
            qr=F(2**v,2**u)
            dr=qr*F(v*v,u*u)
            counts["equality_q"]+=int(qr==2)
            counts["q_disjoint"]+=int(qr>=2)
            counts["d_disjoint"]+=int(dr>=2)
            counts["overlap"]+=int(qr<2 and dr<2)
    return dict(fixed_target_log_coordinates=[72,76],eps="1/72",J=4,q=q,d_bits=d.bit_length(),
                log_d=show(log_d),certificate=certificate,rows=rows,
                rational_dyadic_controls=counts,scope="Finite WinPair arithmetic only. This q=3 is excluded by later host assembly.")
if __name__=="__main__":
    print(json.dumps(test(),indent=2))
