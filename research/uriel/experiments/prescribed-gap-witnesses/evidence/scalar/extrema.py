"""Whole-interval extrema of the actual conductor-one ramp on the fixed target."""
from fractions import Fraction as Q
import json
from prime_mass import S,I,box,log,sqrt_box,ZERO,ONE,euler_gamma,prime_powers

GAP=(8,12)
PP=prime_powers(GAP[1])

def gamma_em(n=256):
    H=sum((Q(1,i) for i in range(1,n+1)),Q(0))
    err=Q(1,240*n**8)
    smooth=Q(1,2*n)-Q(1,12*n**2)+Q(1,120*n**4)-Q(1,252*n**6)+err
    value=box(H-smooth)-log(n)
    return value+I(-box(err).hi,box(err).hi)

def bounds(a,b):
    return I(box(a).lo,box(b).hi)

def linear_coeffs(start,nine=True):
    slope,subtotal=ZERO,ZERO
    for n,p in PP.items():
        if n<=start and (n!=9 or nine):
            slope=slope+log(p).scale(Q(1,n))
            subtotal=subtotal+log(p)
    return slope,subtotal

def signal(a,b,slope,subtotal,gamma,mode):
    root=sqrt_box(bounds(a,b))
    if mode=='ramp_only': g=slope
    else:
        correction=ONE+gamma if mode=='genuine' else ZERO
        g=slope+correction-I(log(a).lo,log(b).hi)
    return root*g-subtotal*root.reciprocal()

def extrema(mode='genuine',nine=True):
    c=gamma_em()
    knots=sorted({8,12,*[n for n in PP if 8<n<12 and (n!=9 or nine)]})
    candidates={}
    segments=[]
    records=[]
    for a,b in zip(knots,knots[1:]):
        A,B=linear_coeffs(a,nine)
        for x in (a,b):
            v=signal(x,x,A,B,c,mode)
            if str(x) in candidates:
                before=candidates[str(x)]
                assert before.lo<=v.hi and v.lo<=before.hi
                v=I(max(before.lo,v.lo),min(before.hi,v.hi))
            candidates[str(x)]=v
        if mode=='ramp_only':
            assert A.lo>0 and B.lo>0
            segments.append(dict(range=[a,b],sign='increasing throughout'))
            continue
        correction=ONE+c if mode=='genuine' else ZERO
        def derivnum(x):
            return (A+correction-box(2)-log(x)).scale(x)+B
        slope_of_numerator=A+correction-box(3)-log(a)
        assert slope_of_numerator.hi<0
        da,db=derivnum(a),derivnum(b)
        assert da.lo>0 or da.hi<0
        assert db.lo>0 or db.hi<0
        row=dict(range=[a,b],left_D=da.pair(12),right_D=db.pair(12),
                 derivative_of_D_upper=slope_of_numerator.pair(12)[1])
        if da.lo>0 and db.hi<0:
            lo,hi=Q(a),Q(b)
            for _ in range(61):
                mid=(lo+hi)/2
                v=derivnum(mid)
                if v.lo>0:lo=mid
                elif v.hi<0:hi=mid
                else:break
            assert derivnum(lo).lo>0 and derivnum(hi).hi<0
            val=signal(lo,hi,A,B,c,mode)
            loc=bounds(lo,hi).pair(14)
            name=f'critical in ({a},{b})'
            row['critical_bracket']=loc
            candidates[name]=val
            records.append((name,loc))
        segments.append(row)
    high=max(candidates,key=lambda k:candidates[k].lo)
    low=min(candidates,key=lambda k:candidates[k].hi)
    assert all(candidates[high].lo>v.hi for key,v in candidates.items() if key!=high)
    assert all(candidates[low].hi<v.lo for key,v in candidates.items() if key!=low)
    initial=candidates['8']
    final=candidates['12']
    largest=candidates[high]
    return dict(mode=mode,include_nine=nine,segments=segments,
                normalized_candidates={k:v.pair(14) for k,v in candidates.items()},
                maximum=dict(location=high,value=largest.pair(14)),minimum=dict(location=low,value=candidates[low].pair(14)),
                maximum_minus_left=(largest-initial).pair(14),maximum_minus_right=(largest-final).pair(14),
                passes_ceiling_one=largest.hi<=S,
                passes_two_thirds=largest.hi<=box(Q(2,3)).lo)

def factors(n):
    out={}
    for p in range(2,n+1):
        while n%p==0:
            out[p]=out.get(p,0)+1
            n//=p
    return out

def independent_integer(x):
    # Reconstruct Lambda(n) symbolically by recursive divisor inversion
    # log(n)=sum_{d|n} Lambda(d). Coordinates are rational coefficients of log p.
    lam={1:{}}
    U={}
    V={}
    for n in range(2,x+1):
        coeff=factors(n)
        for d in range(2,n):
            if n%d==0:
                for p,v in lam[d].items():coeff[p]=coeff.get(p,0)-v
        lam[n]={p:v for p,v in coeff.items() if v}
        for p,v in lam[n].items():U[p]=U.get(p,0)+Q(v)*(Q(x,n)-1)
    for n,p in PP.items():
        if n<=x:V[p]=V.get(p,0)+Q(x,n)-1
    keys=set(U)|set(V)
    assert all(U.get(k,0)==V.get(k,0) for k in keys)
    g=euler_gamma()
    direct=ZERO
    for p,weight in U.items():direct=direct+log(p).scale(weight)
    independent=(direct+(ONE+g-log(x)).scale(x))*sqrt_box(box(x)).reciprocal()
    A,B=linear_coeffs(x)
    target=signal(x,x,A,B,gamma_em(),'genuine')
    assert target.lo>=independent.lo and target.hi<=independent.hi
    return dict(x=x,ramp_coefficients={str(p):str(U.get(p,0)) for p in sorted(keys)},
                normalized=target.pair(14),independent_range=independent.pair(12))

def main():
    fast,slow=gamma_em(),euler_gamma()
    assert slow.lo<fast.lo<=fast.hi<slow.hi
    cases=[extrema(),extrema(nine=False),extrema(mode='no_linear'),extrema(mode='ramp_only')]
    cutoff=Q(5373,10000)
    observed=cases[0]['normalized_candidates']
    assert Q(observed['11'][1])<cutoff and Q(observed['12'][1])<cutoff
    assert Q(observed['critical in (11,12)'][0])>cutoff
    return dict(post_hoc_subinterval={'range':[11,12],'ceiling':str(cutoff),
                'both_ends_pass':True,'interior_witness_exceeds':True},target=GAP,prime_powers={str(n):p for n,p in sorted(PP.items())},
                gamma_fast=fast.pair(21),gamma_harmonic=slow.pair(14),
                integer_controls=[independent_integer(x) for x in range(8,13)],cases=cases)
if __name__=='__main__':
    print(json.dumps(main(),indent=2))
