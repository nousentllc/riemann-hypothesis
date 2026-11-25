"""Exact finite tests of the dyadic six-square density and its neighborhood."""
import argparse
import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def square_histogram(modulus, weights=(1,1,1,1,1,1)):
    ways = [1] + [0]*(modulus-1)
    for weight in weights:
        squares = Counter(weight*x*x % modulus for x in range(modulus))
        result = [0]*modulus
        for offset, multiplicity in squares.items():
            for residue, count in enumerate(ways):
                result[(residue+offset) % modulus] += multiplicity*count
        ways = result
    assert sum(ways) == modulus**len(weights)
    return ways

def valuation(n):
    assert n
    return (n & -n).bit_length()-1

def character(odd):
    assert odd%2
    return 1 if odd%4==1 else -1

def density(n):
    assert n != 0
    t=valuation(n)
    return 1-Fraction(character(n >> t),4**(t+1))

def cylinder(r,b):
    if b==0 or valuation(b)+1>=r:
        return Fraction(1)
    return density(b)

def primitive_base():
    counts=Counter()
    for number_odd in range(1,7):
        even=6-number_odd
        for square_fours in range(even+1):
            patterns=math.comb(6,number_odd)*math.comb(even,square_fours)
            choices=4**number_odd*2**even
            counts[(number_odd+4*square_fours)%8] += patterns*choices
    return [counts[i] for i in range(8)]

def direct(modulus):
    counts=[0]*modulus
    primitive=[0]*modulus
    for xs in itertools.product(range(modulus),repeat=6):
        s=sum(x*x for x in xs)%modulus
        counts[s]+=1
        if any(x%2 for x in xs):
            primitive[s]+=1
    return counts,primitive

def run():
    primitive=primitive_base()
    rows=[]
    previous=None
    cells=0
    for r in range(1,12):
        m=2**r
        counts=square_histogram(m)
        if r<=3:
            ref,prim=direct(m)
            assert counts==ref
            if r==3: assert prim==primitive
        for b,n in enumerate(counts):
            assert Fraction(n,m**5)==cylinder(r,b), (r,b)
            if r>=3 and b!=0:
                assert (m**5*Fraction(primitive[b%8],8**5) +
                        (m**5*Fraction(1,16)*cylinder(r-2,b//4) if b%4==0 else 0))==n
        if previous is not None:
            assert all(counts[b]+counts[b+m//2]==64*old for b,old in enumerate(previous))
        previous=counts
        cells+=m
        rows.append(dict(level=r,modulus=m,cells=m,total=str(sum(counts)),zero=counts[0],
                         at1=counts[1],at3=counts[3] if m>3 else None))
    # At every parent resolving the valuation but not the sign: opposite child biases.
    splits=[]
    for t in range(10):
        left,right=2**t,3*2**t
        a,b=density(left),density(right)
        assert a<1<b and a+b==2 and cylinder(t+1,left)==1
        splits.append(dict(t=t,first=str(a),second=str(b),parent='1'))
    # Independent test of the primitive lifting involution on all r=3 parent tuples.
    paired=0
    for xs in itertools.product(range(8),repeat=6):
        first=next((i for i,x in enumerate(xs) if x%2),None)
        if first is None:continue
        ys=list(xs); ys[first]=(ys[first]+4)%8
        assert (sum(x*x for x in ys)-sum(x*x for x in xs))%16==8
        paired+=1
    assert paired==8**6-4**6
    # Omitting half the trace doubles the output. Test the full pushed-forward histogram.
    m=64
    original=square_histogram(m)
    doubled=square_histogram(m,(2,)*6)
    assert all(n==(0 if b%2 else original[b//2]+original[b//2+m//2]) for b,n in enumerate(doubled))
    # Changing input basis without changing the lattice silently substitutes an index-8 sublattice.
    changed=square_histogram(8,(1,4,1,4,1,4))
    # Compare the last observed finite density with coarser binned densities in Haar norms.
    precision=11
    resolution=[]
    finest=[Fraction(n,(2**precision)**5) for n in previous]
    for r in range(1,precision):
        errors=[abs(v-cylinder(r,i%(2**r))) for i,v in enumerate(finest)]
        l1=sum(errors)/len(errors)
        l2sq=sum(d*d for d in errors)/len(errors)
        assert l1==Fraction(8,7)*(Fraction(1,8**r)-Fraction(1,8**precision))
        assert l2sq==Fraction(32,31)*(Fraction(1,32**r)-Fraction(1,32**precision))
        assert max(errors)==Fraction(1,4**r)
        resolution.append(dict(level=r,finite_l1=str(l1),finite_l2_squared=str(l2sq),finite_max=str(max(errors))))
    # Sharp global modulus for the continuous density representative, with value one at zero.
    equality=0
    for a,b in itertools.combinations(range(128),2):
        da=density(a) if a else 1
        db=density(b)
        normalized=abs(da-db)*4**valuation(b-a)
        assert normalized<=2
        equality+=int(normalized==2)
    return dict(holder_pairs=math.comb(128,2),holder_equalities=equality,resolution=resolution,levels=rows,all_cells=cells,brute_force_moduli=[2,4,8],primitive_mod8=primitive,
                primitive_mod8_densities=[str(Fraction(n,8**5)) for n in primitive],
                paired_primitive_tuples=paired,opposite_children=splits,
                even_square_factors=[str(density(4**e)) for e in range(7)],
                doubled_output_mod64=dict(at1=doubled[1],at2_density=str(Fraction(doubled[2],64**5))),
                alternate_basis_mod8=dict(weights=[1,4,1,4,1,4],at1=changed[1],
                                          density=str(Fraction(changed[1],8**5))))
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=run()
    p=ROOT/'experiment.json'
    if args.write: p.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(p.read_text())==result
    print(result['all_cells'],result['primitive_mod8_densities'],result['paired_primitive_tuples'],result['doubled_output_mod64'],result['alternate_basis_mod8'])
