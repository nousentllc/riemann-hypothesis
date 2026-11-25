"""Exact cyclic convolution on the two coefficient groups by NTT and CRT."""
from fractions import Fraction
from math import prod
from pathlib import Path
import json
import sys

PRIMES = [(998244353, 3), (1004535809, 3), (469762049, 3), (167772161, 3)]
UNITS = [(1, 0), (1, 1), (3, 1), (1, 3)]


def transform(values, p, generator):
    """Unnormalized positive-exponent transform; validate the root's order."""
    n = len(values)
    root = pow(generator, (p-1)//n, p)
    assert (p-1)%n == 0 and pow(root, n//2, p) == p-1
    out = list(values)
    j = 0
    for i in range(1,n):
        bit = n//2
        while j & bit:
            j ^= bit
            bit >>= 1
        j ^= bit
        if i < j:
            out[i],out[j] = out[j],out[i]
    width = 2
    while width <= n:
        half = width//2
        step = pow(root,n//width,p)
        for start in range(0,n,width):
            w = 1
            for i in range(start,start+half):
                a,b = out[i], w*out[i+half] % p
                out[i],out[i+half] = (a+b)%p,(a-b)%p
                w = w*step%p
        width *= 2
    return out


def census(depth, targets, common_power):
    rows,cols = 2**((depth+1)//2), 2**(depth//2)
    addresses = {(a%rows,b%cols) for a,b in targets}
    square = [[0]*cols for _ in range(rows)]
    for a in range(0,rows,2**((common_power+1)//2)):
        for b in range(0,cols,2**(common_power//2)):
            square[(a*a+2*b*b)%rows][2*a*b%cols] += 1
    bound = sum(map(sum,square))**6
    result = dict.fromkeys(addresses,0)
    product = 1
    for p,g in PRIMES:
        first = [transform(row,p,g) for row in square]
        spectrum = [[pow(x,6,p) for x in transform(column,p,g)] for column in zip(*first)]
        assert spectrum[0][0] == bound%p
        rx,ry = pow(g,(p-1)//rows,p),pow(g,(p-1)//cols,p)
        inv_size,inv_product = pow(rows*cols,-1,p),pow(product,-1,p)
        for a in {a for a,_ in addresses}:
            weights = [pow(rx,(-a*i)%rows,p) for i in range(rows)]
            partial = [sum(x*y for x,y in zip(col,weights))%p for col in spectrum]
            for ax,b in addresses:
                if ax == a:
                    residue = inv_size*sum(x*pow(ry,(-b*j)%cols,p) for j,x in enumerate(partial))%p
                    result[a,b] += product*((residue-result[a,b])*inv_product%p)
        product *= p
        if product > bound:
            break
    assert product > bound and all(0<=v<=bound for v in result.values())
    return {t:result[t[0]%rows,t[1]%cols] for t in targets}


def target(k, u):
    a,b = u
    return 4**k*(a*a+2*b*b),4**k*2*a*b


def run():
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'literature'))
    from ramified_probe import counts, moduli
    targets = {(0,0),(1,0),(0,1)} | {target(k,u) for k in range(1,5) for u in UNITS}
    targets.update((4**k,4**k) for k in range(1,5))
    report = []
    for d in (5,6,8,9,10,12,13,14,16,17,18):
        total,inner = (census(d,targets,even) for even in (False,True))
        denom = 2**(5*d)
        if d<=10:
            mx,my = moduli(d)
            for even,observed in ((False,total),(True,inner)):
                ref = counts(d,6,divisible=even)
                assert all(n==ref[a%mx,b%my] for (a,b),n in observed.items())
        assert total[0,1]==0 and Fraction(total[1,0],denom)==2
        entries = {}
        for k in range(1,5):
            t = target(k,UNITS[0])
            assert all((inner[t],total[t])==(inner[target(k,u)],total[target(k,u)]) for u in UNITS)
            mass = Fraction(total[t],denom)
            primitive = Fraction(total[t]-inner[t],denom)
            assert primitive == Fraction(15,8)
            expected = 2+Fraction(2,256**k)
            if d>=4*k+2:
                assert mass==expected
            if d==4*k+1:
                assert mass!=expected
            companion = Fraction(total[4**k,4**k],denom)
            if d == 4*k+2:
                assert (mass+companion)/2==2
            entries[str(k)] = dict(count=total[t],primitive=str(primitive),companion=str(companion),
                                   all_divisible=str(Fraction(inner[t],denom)),total=str(mass))
        report.append(dict(uniformizer_depth=d,denominator=denom,targets=entries))
    assert prod(p for p,_ in PRIMES)>2**108
    tail_counts = [census(10,{(16,0)},j)[16,0] for j in range(6)]
    shells = [Fraction(a-b,2**50) for a,b in zip(tail_counts,tail_counts[1:])]
    assert tail_counts[-1]==0
    assert shells==[Fraction(15,8),Fraction(15,128),Fraction(15,2048),Fraction(1,2048),Fraction(1,32768)]
    return dict(target16_shell_counts=tail_counts, target16_exact_shell_densities=list(map(str,shells)), method='finite Fourier transform and exact CRT reconstruction',dimension=6,
                unit_coefficients=UNITS,rows=report)


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
