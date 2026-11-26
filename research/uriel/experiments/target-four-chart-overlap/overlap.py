"""Exact tests over (Z/2^n)[pi]/(pi^2-2). An index a + M*b stores a+b*pi."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json


class Ring:
    def __init__(self, depth):
        self.m = 2**depth
        self.size = self.m**2
        self.elements = range(self.size)
        self.depth = depth

    def pack(self, a, b):
        return (a % self.m) + self.m*(b % self.m)

    def coordinates(self, x):
        return x % self.m, x // self.m

    def add(self, x, y):
        a,b = self.coordinates(x)
        c,d = self.coordinates(y)
        return self.pack(a+c,b+d)

    def neg(self, x):
        a,b = self.coordinates(x)
        return self.pack(-a,-b)

    def sub(self, x, y):
        return self.add(x,self.neg(y))

    def scale(self, k, x):
        a,b = self.coordinates(x)
        return self.pack(k*a,k*b)

    def sq(self, x):
        a,b = self.coordinates(x)
        return self.pack(a*a+2*b*b,2*a*b)

    def polynomial(self, x, linear, quadratic):
        return self.add(self.scale(linear,x),self.scale(quadratic,self.sq(x)))


def physical_square(r, index, center, width):
    # Square the cleared physical coordinate, subtract its constant, then divide by 512.
    a,b = r.coordinates(index)
    x,y = center+width*a,width*b
    real,imag = x*x+2*y*y-center*center,2*x*y
    assert real%512==imag%512==0
    return r.pack(real//512,imag//512)


def inverse_a_by_lifts(depth):
    table={0:(0,0)}
    for n in range(1,depth+1):
        r=Ring(n)
        old=Ring(n-1)
        nxt={}
        for target in r.elements:
            c,d=r.coordinates(target)
            a,b=table[old.pack(c,d)]
            candidates=[(a+i*old.m,b+j*old.m) for i,j in product(range(2),repeat=2)]
            hits=[p for p in candidates if r.polynomial(r.pack(*p),-3,32)==target]
            assert len(hits)==1
            nxt[target]=hits[0]
        table=nxt
    return [r.pack(*table[t]) for t in r.elements]


def inverse_b_by_iteration(r):
    answers=[]
    for t in r.elements:
        x=0
        for _ in range(r.depth):
            x=r.sub(t,r.scale(2,r.sq(x)))
        assert r.polynomial(x,1,2)==t
        answers.append(x)
    return answers


def checks(depth, full=False):
    r=Ring(depth)
    ia=inverse_a_by_lifts(depth)
    ib=inverse_b_by_iteration(r)
    xs=[physical_square(r,i,-6,128) for i in r.elements]
    ys=[physical_square(r,i,8,32) for i in r.elements]
    zs=[physical_square(r,i,0,32) for i in r.elements]
    assert len(set(ia))==len(set(ib))==r.size
    assert all(xs[ia[t]]==ys[ib[t]]==t for t in r.elements)
    if not full and depth>4:
        return dict(depth=depth,pivot_residues_each=r.size)
    # Exhaustively evaluate the physical pivot pairs, independently of either inverse solver.
    physical=[set() for _ in r.elements]
    for u,v in product(r.elements,repeat=2):
        physical[r.add(xs[u],ys[v])].add((u,v))
    @lru_cache(None)
    def compare(t):
        xset={(ia[r.sub(t,r.polynomial(v,1,2))],v) for v in r.elements}
        yset={(u,ib[r.sub(t,r.polynomial(u,-3,32))]) for u in r.elements}
        assert len(xset)==len(yset)==r.size and xset==yset==physical[t]
        return xset
    for t in r.elements:
        compare(t)
    rows=[]
    if full:
        for digits in ((0,0),(1,0),(0,1),(1,1)):
            t=r.pack(*digits)
            total=both=miss=coupled=0
            digest=sha256()
            # Distinct transverse indices label disjoint fibers, so pairwise set equality
            # for every label verifies the six-dimensional image sets without storing them.
            for z in product(r.elements,repeat=4):
                off=0
                for i in z:
                    off=r.add(off,zs[i])
                key=r.sub(t,off)
                pairs=compare(key)
                total+=len(pairs)
                digest.update(bytes([*z,key]))
                for u,v in sorted(pairs):
                    a,b=r.coordinates(u)
                    c,d=r.coordinates(v)
                    both+=int(a%2==b%2==c%2==d%2==0)
                    miss+=int(a%2==1 and b%2==c%2==d%2==0)
                    # A coupled restriction sees both pivot variables and a transverse digit.
                    coupled+=int((a+c+r.coordinates(z[0])[0])%r.m==0 and b%2==0)
            assert total==r.size**5
            assert both==(r.size**5//4 if digits==(0,0) else 0)
            assert miss==(r.size**5//4 if digits==(1,0) else 0)
            rows.append(dict(t=digits,total=total,both_even=both,shifted_pivot=miss,
                             coupled=coupled,transverse_key_digest=digest.hexdigest()))
    return dict(depth=depth,pivot_residues_each=r.size,physical_pairs=r.size**2,
                all_pair_fibers_checked=r.size,full_targets=rows)


def boundary():
    # Widen physical y from 32/5 to 16/5, normalize its target by 256.
    # Then the exact polynomial is v+v². Roots 0 and -1 give opposite y.
    data=[]
    for n in range(1,6):
        r=Ring(n)
        hist=Counter(r.polynomial(v,1,1) for v in r.elements)
        zeros=sum(1 for v in r.elements if r.polynomial(v,1,1)==0)
        assert r.polynomial(r.pack(-1,0),1,1)==0 and zeros>=2
        data.append(dict(depth=n,domain=r.size,image=len(hist),zero_preimages=zeros,
                         multiplicities=dict(sorted(Counter(hist.values()).items()))))
    return data


def run():
    x=Fraction(-6,5); y=Fraction(8,5)
    assert x*x+y*y==4 and (x-2)/8==Fraction(-2,5)
    scalar_x=16*Fraction(1,4)**25
    scalar_y=256*Fraction(1,4)**27
    wrong_y=16*Fraction(1,4)**27
    assert scalar_x==scalar_y==Fraction(1,2**46) and wrong_y*16==scalar_y
    return dict(center=[str(x),str(y)],tests=[checks(n,n<=2) for n in (1,2,3,4,6,8)],
                scalar=str(scalar_x),split=str(scalar_x/2),wrong_y=str(wrong_y),
                boundary=boundary())


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
