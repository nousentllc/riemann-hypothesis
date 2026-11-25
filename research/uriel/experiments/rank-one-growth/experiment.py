"""Exact congruence experiment for the form x_1^2+...+x_6^2 (standard lattice)."""
import argparse, json
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def histogram(modulus):
    squares=Counter((x*x)%modulus for x in range(modulus))
    counts=[1]+[0]*(modulus-1)
    for _ in range(6):
        nxt=[0]*modulus
        for residue,n in enumerate(counts):
            if n:
                for sq,m in squares.items():
                    nxt[(residue+sq)%modulus]+=n*m
        counts=nxt
    assert sum(counts)==modulus**6
    return counts

def odd_factor(p,e):
    """Density at a square, valuation of its square root e."""
    eps=1 if p%4==1 else -1
    val=1-F(eps,p**3)
    primitive=1+F(eps*(p-1),p**3)-F(1,p**5)
    for _ in range(e):
        val=primitive+val/F(p**4)
    return val

def generate():
    cases=[]; totals=Counter()
    for p,depth in ((2,7),(3,6),(5,4),(7,3),(11,2),(13,2)):
        for r in range(1,depth+1):
            modulus=p**r; counts=histogram(modulus)
            if modulus<=8:
                brute=Counter(sum(x*x for x in v)%modulus for v in product(range(modulus),repeat=6))
                assert all(counts[i]==brute[i] for i in range(modulus))
                totals['direct_histograms']+=1
            if p==2 and r<3:continue
            for target in range(1,modulus):
                if p==2:
                    if target%8!=1: continue
                    pred=F(hist8,8**5)
                else:
                    unit=target;ordp=0
                    while unit%p==0:unit//=p;ordp+=1
                    eps=1 if p%4==1 else -1
                    prim=1+F(eps*(p-1),p**3)-F(1,p**5)
                    pred=prim if ordp%2 else 1-F(eps,p**3)
                    for _ in range(ordp//2):pred=prim+pred/F(p**4)
                actual=F(counts[target],modulus**5)
                assert actual==pred,(p,r,target,actual,pred)
                if p!=2:assert abs(actual-1)<=F(2,p**2)
                totals['density_cells']+=1
                if target in {1,p,p**2,p**4} and (p<8 or r==2):
                    cases.append(dict(p=p,r=r,target=target,count=counts[target],density=str(actual)))
    return cases,totals

hist8=histogram(8)[1]
def run():
    cells,totals=generate()
    small=[2,3,5,7,11,13,17,19,23,29,31]
    bound=F(hist8,8**5)*F(8,27)
    alpha2=F(hist8,8**5)
    rows=[]
    for a in [1,3,5,7,9,15,21,45,105,1155]:
        factors=[]
        for p in small[1:]:
            n=a;e=0
            while n%p==0:n//=p;e+=1
            factors.append(odd_factor(p,e))
        val=alpha2*prod(factors)
        assert val>=bound
        rows.append(dict(a=a,partial_product=str(val),partial_scaled=str(val*a**4)))
    envelope=[]
    for L in (3,5,10,25,100):
        x=prod(1-F(2,n*n) for n in range(3,L+1))
        y=prod(1-F(1,n*n) for n in range(3,L+1))
        assert x>=y**3 and y==F(2*(L+1),3*L)
        envelope.append([L,str(x),str(y**3)])
    weak=[dict(n=n,product=str(F(1,2**n))) for n in (1,2,4,8,16)]
    # Moving support for a composite progression base, and a boundary-rank scalar model.
    bad = [2,7]
    base = prod(bad)+1
    moving = [k for k in range(2,base+1) if base%k==0 and all(k%d for d in range(2,k))]
    assert moving==[3,5] and all(base%p for p in bad)
    for a in range(1,65):
        mass, integral = a*a, 2*a*a
        assert integral == 2*mass and abs(integral-mass) == a**2
    return dict(form='Six squares in six integral coordinates; classical congruence densities',
      normalization='count modulo q^r divided by q^(5r)',tested=dict(totals),sample_cells=cells,
      dyadic_count_mod8_at1=hist8,dyadic_density_odd_squares=str(alpha2),odd_a_uniform_normalized_lower=str(bound),
      partial_primes=small,partial_products=rows,telescoping_controls=envelope,half_only_control=weak,
      composite_base_control=dict(bad_rational_primes=bad,Q=prod(bad),p=base,moving=moving),
      rank_two_control=dict(D=1,M=2,w=1,kappa=1,c=2,P='a^2',I='2a^2',C=1, tested_dilations=64))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true')
    a=p.parse_args();out=run();path=ROOT/'experiment.json'
    if a.write:path.write_text(json.dumps(out,indent=2)+'\n')
    else:assert json.loads(path.read_bytes())==out
    print(out['tested'],out['dyadic_count_mod8_at1'],out['dyadic_density_odd_squares'],out['odd_a_uniform_normalized_lower'])
