"""Exact base discriminant, Minkowski cutoff, small-prime factorization, and Bernoulli controls."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, gcd, isqrt
import json


def determinant(a):
    """Fraction-free elimination; swaps preserve the determinant sign."""
    a=[row[:] for row in a]
    sign=1
    previous=1
    for k in range(len(a)-1):
        if a[k][k]==0:
            pivot=next((j for j in range(k+1,len(a)) if a[j][k]),None)
            if pivot is None:
                return 0
            a[k],a[pivot]=a[pivot],a[k]
            sign=-sign
        pivot=a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                value,remainder=divmod(pivot*a[i][j]-a[i][k]*a[k][j],previous)
                assert remainder==0
                a[i][j]=value
        previous=pivot
    return sign*a[-1][-1]


def sylvester_res(f,g):
    m,n=len(f)-1,len(g)-1
    matrix=[[0]*i+f+[0]*(n-i-1) for i in range(n)]
    matrix += [[0]*i+g+[0]*(m-i-1) for i in range(m)]
    return determinant(matrix)


def arctan_inverse(d,steps):
    terms=[F((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(steps+1)]
    value=sum(terms[:-1])
    return sorted((value,value+terms[-1]))


def decimal_bounds(lo,hi,digits):
    unit=10**digits
    def display(n):
        return f"{n//unit}.{n%unit:0{digits}}"
    return [display((lo*unit).__floor__()),display((hi*unit).__ceil__())]


def minkowski():
    a,b=arctan_inverse(5,20)
    c,d=arctan_inverse(239,5)
    lower_pi,upper_pi=16*a-4*d,16*b-4*c
    places=10**26
    root=isqrt(16807*places**2)
    low_sqrt,high_sqrt=F(root,places),F(root+1,places)
    factor=F(factorial(6),6**6)
    lo,hi=(4/upper_pi)**3*factor*low_sqrt,(4/lower_pi)**3*factor*high_sqrt
    loose=F(40,31)**3*factor*130
    assert 4<lo<hi<loose<5
    return dict(interval=decimal_bounds(lo,hi,15),floor=4,lean_upper=str(loose),
                square_root_enclosure=decimal_bounds(low_sqrt,high_sqrt,15),
                pi_enclosure=decimal_bounds(lower_pi,upper_pi,15))


def divpoly(a,b,p):
    """Long division of ascending-coefficient polynomials by a monic polynomial."""
    a=[v%p for v in a]
    quotient=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b):
        offset=len(a)-len(b)
        quotient[offset]=c=a[-1]
        for i,z in enumerate(b):
            a[offset+i]=(a[offset+i]-c*z)%p
        while a and not a[-1]:
            a.pop()
    return quotient,a


def factors(f,p):
    for degree in range(1,(len(f)-1)//2+1):
        for low in product(range(p),repeat=degree):
            trial=[*low,1]
            q,r=divpoly(f,trial,p)
            if not r:
                return [trial]+factors(q,p)
    return [f]


def order(a,n):
    assert gcd(a,n)==1
    power=a%n;count=1
    while power!=1:
        power=power*a%n;count+=1
    return count


def bernoulli(n):
    values=[F(1)]
    for k in range(1,n+1):
        values.append(-sum(comb(k+1,j)*v for j,v in enumerate(values))/(k+1))
    return values


def research():
    f=[1]*7
    g=[6,5,4,3,2,1]
    disc=-(sylvester_res(f,g))
    assert disc==-7**5
    fact={}
    for p in (2,3,7):
        fs=factors(f,p)
        product_f=[1]
        for factor in fs:
            acc=[0]*(len(product_f)+len(factor)-1)
            for i,y in enumerate(product_f):
                for j,z in enumerate(factor):
                    acc[i+j]=(acc[i+j]+y*z)%p
            product_f=acc
        assert product_f==f
        if p!=7:
            assert all(len(a)-1==order(p,7) for a in fs)
        else:
            assert fs==[[6,1]]*6
        fact[str(p)]=fs
    orders=[dict(conductor=q,residue_degrees={str(p):order(p,q) for p in [2,3,5,13,29]})
            for q in [7,49,343]]
    B=bernoulli(34)
    irregular={str(p):[i for i in range(2,p-2,2) if B[i].numerator%p==0] for p in [7,37]}
    assert irregular=={"7":[],"37":[32]}
    return dict(discriminant=disc,uniformizer_norm=sum(f),minkowski=minkowski(),
                polynomial_factors_ascending= fact,orders=orders,
                bernoulli_numerators={str(i):B[i].numerator for i in (2,4,32)},irregular_indices=irregular)


if __name__=='__main__':
    print(json.dumps(research(),indent=2))
