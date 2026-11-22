"""Post-hoc fixed-point enclosure of the conductor-one maximum on [256,4096]."""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from math import isqrt
from prime_windows import trial_prime_base

S = 2**128
NTERMS = 44
LOW = F("0.1177870105")
HIGH = F("0.1177870108")
WITNESS = F("300.25283")


def ceilq(n,d):
    return -(-n//d)


@dataclass(frozen=True)
class Interval:
    """Closed interval [lo/S,hi/S]. All endpoints and arithmetic operations are integer."""
    lo: int
    hi: int

    @staticmethod
    def of(x):
        q=F(x)*S
        return Interval(q.numerator//q.denominator,ceilq(q.numerator,q.denominator))

    def __add__(self,b):
        return Interval(self.lo+b.lo,self.hi+b.hi)

    def __sub__(self,b):
        return Interval(self.lo-b.hi,self.hi-b.lo)

    def __mul__(self,b):
        corners=(self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi)
        return Interval(min(corners)//S,ceilq(max(corners),S))

    def times(self,q):
        q=F(q)
        a,b=sorted((self.lo*q.numerator,self.hi*q.numerator))
        return Interval(a//q.denominator,ceilq(b,q.denominator))

    def reciprocal(self):
        if self.lo<=0:
            raise ValueError("Positive interval required")
        return Interval(S*S//self.hi,ceilq(S*S,self.lo))


def log_unit(q):
    """log(q) via the atanh series for 1 <= q <= 2 with a geometric tail bound."""
    q=F(q)
    if not 1<=q<=2:
        raise ValueError("Log range reduction failed")
    t=Interval.of((q-1)/(q+1))
    t2=t*t
    term=t
    total=Interval.of(0)
    for j in range(NTERMS):
        total=total+term.times(F(2,2*j+1))
        term=term*t2
    tail=F(2, (2*NTERMS+1)*3**(2*NTERMS+1))/(1-F(1,9))
    return Interval(total.lo,total.hi+Interval.of(tail).hi)


@cache
def logarithm(q):
    q=F(q)
    if q<1:
        raise ValueError("This certificate uses logarithms at arguments >= 1")
    k=q.numerator.bit_length()-q.denominator.bit_length()
    if q<2**k:
        k-=1
    return log_unit(q/2**k)+log_two().times(k)


@cache
def log_two():
    return log_unit(F(2))


def sqrt_interval(q):
    q=F(q)*S*S
    low=isqrt(q.numerator//q.denominator)
    return Interval(low,low+int(low**2*q.denominator<q.numerator))


@cache
def gamma_interval(n=1_000_000):
    # Sum independent lower and upper bounds on each 1/k.
    h=sum(S//k for k in range(1,n+1))
    approx=Interval(h,h+n)-logarithm(F(n))
    # The telescoping tail is sum_{k>=n} integral_k^(k+1) (t-k)/t^2 dt.
    upper=F(1,2*n)+F(1,2*n*n)
    lower=F(1,2*(n+1))
    return Interval(approx.lo-Interval.of(upper).hi,approx.hi-Interval.of(lower).lo)


def difference(y,A,B,C):
    root=sqrt_interval(y)
    slope_part=A-logarithm(y)
    value=slope_part.times(y)-B-root.times(C)
    derivative=slope_part-Interval.of(1)-root.reciprocal().times(C/2)
    return value,derivative


def run():
    left,right=256,4096
    if HIGH<=0 or HIGH>=4*isqrt(left):
        raise ValueError("Concavity precondition failed")
    powers={n:p for n in range(2,right+1) if (p:=trial_prime_base(n))}
    knots=[left]+[n for n in powers if left<n<right]+[right]
    A=Interval.of(1)+gamma_interval()
    B=Interval.of(0)
    for n,p in powers.items():
        if n<=left:
            A=A+logarithm(F(p)).times(F(1,n))
            B=B+logarithm(F(p))

    accepted=0
    deepest=0
    largest_tangent=None
    lower_witness=None
    endpoint_bounds=[]
    for x,z in zip(knots,knots[1:]):
        if x<=WITNESS<=z:
            lower_witness=difference(WITNESS,A,B,LOW)[0].lo
        for endpoint in {left,right}.intersection({x,z}):
            endpoint_bounds.append(difference(F(endpoint),A,B,F("0.10712985"))[0].hi)
        todo=[(F(x),F(z),0)]
        while todo:
            a,b,depth=todo.pop()
            midpoint=(a+b)/2
            value,derivative=difference(midpoint,A,B,HIGH)
            top=value.hi+Interval(0,max(abs(derivative.lo),abs(derivative.hi))).times((b-a)/2).hi
            if top<0:
                accepted+=1
                deepest=max(deepest,depth)
                largest_tangent=top if largest_tangent is None else max(largest_tangent,top)
            elif depth<40:
                todo.extend(((a,midpoint,depth+1),(midpoint,b,depth+1)))
            else:
                raise ValueError(f"Upper certificate inconclusive on {a} .. {b}")
        if z in powers:
            A=A+logarithm(F(powers[z])).times(F(1,z))
            B=B+logarithm(F(powers[z]))
    if lower_witness is None or lower_witness<=0 or len(endpoint_bounds)!=2 or max(endpoint_bounds)>=0:
        raise ValueError("Lower witness or endpoint bound inconclusive")
    return dict(window=[left,right],lower=str(LOW),upper=str(HIGH),lower_point=str(WITNESS),
                endpoint_upper=str(F("0.10712985")),fixed_point_denominator=str(S),log_series_terms=NTERMS,
                harmonic_terms=1_000_000,gamma_lo_units=gamma_interval().lo,gamma_hi_units=gamma_interval().hi,
                pieces=len(knots)-1,certified_leaves=accepted,deepest_bisection=deepest,
                largest_D_upper_units=largest_tangent,lower_witness_D_lower_units=lower_witness,
                endpoint_D_upper_units=endpoint_bounds)
