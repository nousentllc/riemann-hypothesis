"""Finite residue exceptions, exact real-interval tests in base-two coordinates, and Euclidean cuts."""
from fractions import Fraction as F
from itertools import product
from math import lcm


def moduli(ell,Z):
    if ell < 2 or Z < 1:
        raise ValueError("Expected a base >= 2 and positive Z")
    weak = 1
    while weak*ell <= Z:
        weak *= ell
    return weak,weak*ell


def near(center,modulus,Z):
    first = 1+(center-1)%modulus
    return range(first,Z+1,modulus)


def compare_power_two(e,p):
    """Sign of e−2^p for positive integer e and nonnegative rational p."""
    p = F(p)
    a,b = e**p.denominator,1<<p.numerator
    return (a>b)-(a<b)


def good_interval(y,exc):
    # Bad iff [y,2y] intersects [log2(e)/2,log2(e)), with e>=2.
    return all(e<=1 or compare_power_two(e,y)<=0 or compare_power_two(e,4*y)>0 for e in exc)


def select(R,U,exc):
    """Window1 at B=2 lifted to integer indices, using comparisons without rounding log2."""
    exc = set(exc)
    if len(exc)>R or U<=0:
        raise ValueError("Cardinality cap or upper scale violated")
    top = F(U)
    while R:
        hit = next((e for e in sorted(exc) if e>1 and
                    compare_power_two(e,top/2)>0 and compare_power_two(e,2*top)<=0),None)
        if hit is None:
            break
        exc.remove(hit)
        R -= 1
        top /= 4
    return top/2


def cohomology():
    local = []
    for ell in (2,3,5,7):
        for Z in sorted({z for p in range(4) for z in (ell**p-1,ell**p,ell**p+1) if z>=1}):
            weak,strict = moduli(ell,Z)
            strict_max = max(len(near(c,strict,Z)) for c in range(strict))
            weak_max = max(len(near(c,weak,Z)) for c in range(weak))
            local.append(dict(ell=ell,Z=Z,strict_modulus=strict,weak_modulus=weak,
                              strict_max=strict_max,weak_max=weak_max))
    inputs = [(4,32,[(2,[1,16,16]),(3,[2,8]),(5,[3])]),
              (8,256,[(2,[0,257]),(3,[16,64]),(7,[16,256])]),
              (8,33,[(2,[32]),(3,[31]),(5,[30])]),(8,8,[])]
    for U in (4,8,12):
        inputs.append((U,2**U,[(2,[2**U])]))
    combined = []
    for U,Z,groups in inputs:
        per_prime = {}
        for ell,centers in groups:
            modulus = moduli(ell,Z)[1]
            per_prime[str(ell)] = sorted({e for c in centers for e in near(c,modulus,Z)})
        E = set().union(*per_prime.values())
        cap = sum(len(cs) for _,cs in groups)
        y = select(cap,U,E)
        combined.append(dict(U=U,Z=Z,centers={str(p):a for p,a in groups},exception_sets=per_prime,
                             union=sorted(E),R=cap,y=str(y),in_range=F(U,2**(cap+2)*2**cap)<=y and 2*y<=U,
                             each_good=all(good_interval(y,s) for s in per_prime.values()),
                             union_good=good_interval(y,E),naive_good=good_interval(F(U,2),E)))
    return dict(prime_ranges=local,combined=combined,
                collision=dict(ell=2,Z=7,center=1,strict=list(near(1,8,7)),weak=list(near(1,4,7))))


def det(matrix):
    A = [list(map(F,row)) for row in matrix]
    d = F(1)
    for j in range(len(A)):
        pivot = next((i for i in range(j,len(A)) if A[i][j]),None)
        if pivot is None:
            return F(0)
        if pivot!=j:
            A[j],A[pivot]=A[pivot],A[j]
            d = -d
        v = A[j][j]
        d *= v
        for i in range(j+1,len(A)):
            c = A[i][j]/v
            for h in range(j+1,len(A)):
                A[i][h] -= c*A[j][h]
    return d


def dot(u,v):
    return sum(a*b for a,b in zip(u,v))


def gram_det(rows):
    return det([[dot(u,v) for v in rows] for u in rows])


def lattice(dim,q):
    v = [1,q]+[0]*(dim-2)
    g = dot(v,v)
    basis = [[-v[j] if i==0 else int(i==j) for i in range(dim)] for j in range(1,dim)]
    P = [[int(i==j)-F(v[i]*v[j],g) for j in range(dim)] for i in range(dim)]
    den = lcm(*(a.denominator for row in P for a in row))
    gd,bd = gram_det(basis),gram_det([v])
    index = abs(det(basis+[v]))
    delta = F(1,3*dim)
    return dict(dim=dim,q=q,delta=str(delta),rank_ok=delta<=F(1,12) and 1<=3*delta*dim,
                projector_denominator=den,expected_g=g,idempotent=all(
                    dot(P[i],[P[h][j] for h in range(dim)])==P[i][j] for i,j in product(range(dim),repeat=2)),
                symmetric=all(P[i][j]==P[j][i] for i,j in product(range(dim),repeat=2)),
                good_gram=str(gd),bad_gram=str(bd),index=str(index),covolume_product_squared=str(gd*bd),
                index_identity=gd*bd==index**2,exact_cut=gd*bd==den**2,
                omit_denominator_cut_holds=gd<=1)


def slopes():
    dg,db,mu,m,lg,Q,delta = 3,1,-1,1,1,1,F(1,12)
    mug = F((dg+db)*mu-db*(m+lg),dg)
    witnesses = [dict(constant=str(c),bound=str(mu-c*delta*Q),holds=mu-c*delta*Q<=mug)
                 for c in (F(9),F(11),F(11999,1000),F(12))]
    return dict(boundary=dict(dg=dg,db=db,mu=mu,m=m,lg=lg,Q=Q,delta=str(delta),mug=str(mug),
                              required_constant=str((mu-mug)/(delta*Q)),tests=witnesses),
                lattices=[lattice(dim,q) for dim,q in product((4,8),(1,2,10,100))])
