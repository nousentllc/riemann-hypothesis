"""Exact synthetic controls for the Frobenius window accounting."""

from collections import Counter
from fractions import Fraction as Q
from math import ceil
import json


def predecessor(n, points, y):
    return next((d for d in range(1, n+1)
                 if (y-d)%n in points and ((y-d)%n)%2 == 0), 0)


def slots(n, points):
    return {((y-d)%n, d):y for y in sorted(points) if y%2
            if (d:=predecessor(n, points, y))}


def mask_census(n):
    totals = Counter()
    max_charge = 0
    for mask in range(1<<n):
        points = {j for j in range(n) if mask>>j&1}
        matched = slots(n,points)
        odd_with_predecessor = sum(y%2 and any(s%2==0 for s in points) for y in points)
        assert len(matched)==odd_with_predecessor
        first_targets = {((y-1)%n,y) for y in points if y%2 and (y-1)%n in points}
        actual_first = {(s,y) for (s,e),y in matched.items() if e==1}
        assert first_targets==actual_first
        for (s,d),y in matched.items():
            assert s in points and s%2==0 and d%2==1 and d<n
            assert (s+d)%n==y
            totals['matched_slots']+=1
            totals['wraparound_slots']+=int(s>y)
        count = sum(t%2 and (t+1)%n in points and
                    any((t+d)%n in points for d in range(3,n,2)) for t in points)
        totals['oriented_collision_masks']+=int(count>0)
        totals['collisions_with_no_distance_one_tau']+=int(count>0 and not actual_first)
        totals['collisions_with_distance_one_tau']+=int(count>0 and bool(actual_first))
        max_charge=max(max_charge,len(matched))
    return {'period':n,'masks':1<<n,'max_charge':max_charge,**totals}


def tent_census(y):
    def plus(x):
        return max(Q(0),x)
    pos = 0
    pair_support = 0
    maximum = Q(0)
    for n in range(1,y+1):
        first,middle,last=(plus(1/Q(n)-s/y) for s in (Q(2),Q(5,2),Q(3)))
        k=first-2*middle+last
        assert k==plus(min(1/Q(n)-2/Q(y),3/Q(y)-1/Q(n)))
        assert 0<=k<=min(1/Q(2*y),1/Q(n))
        assert (k>0)==(Q(y,3)<n<Q(y,2))
        pos+=int(k>0)
        pair_support+=int(first-last>0)
        maximum=max(maximum,k)
    return {'cutoff':y,'inputs':y,'tent_nonzero':pos,
            'two_endpoint_nonzero':pair_support,'peak':str(maximum)}


def orbit(n, T, p, a, b, c_g, lift, loss, price, tau_overhead):
    u=a-2*c_g
    retained_cap=b+20+lift
    empty_cap=25+lift
    assert u/Q(p**3)<min(retained_cap,empty_cap)
    gamma=Q(p,p*p-1)
    kept=Q(0)
    even_minima=Q(0)
    odd_minima=Q(0)
    excluded=Q(0)
    certifying=Q(0)
    for t in T:
        retained=(t+1)%n in T
        c=retained_cap if retained else empty_cap
        d=max(Q(0),u/p-c)
        m=gamma*u-u/p+min(u/p,c)
        if retained:
            excluded+=d
            if t%2 and any((t+j)%n in T for j in range(3,n,2)):
                certifying+=d
        else:
            kept+=d
        if t%2:
            odd_minima+=m
        else:
            even_minima+=m
    g0=kept-loss
    gu=len(T)*gamma*u-odd_minima-loss
    assert gu-g0==excluded+even_minima
    backward=slots(n,T)
    tau_head=sum(min(b,a/Q(p**d)) for s,d in backward)
    matched_minima=sum(min(retained_cap,u/Q(p**d)) for s,d in backward)
    assert tau_head<=matched_minima+len(backward)*2*c_g
    assert matched_minima<=even_minima
    gap=gu-price-max(g0,0)
    assert gap>=certifying+tau_head-price-loss-len(T)*2*c_g
    return {'tau_head':tau_head,'tau_row':Q(ceil(tau_head+tau_overhead)+3),
            'g0':g0,'gU':gu,'premium':max(Q(0),gap),'oriented_first_credit':certifying,
            'matched_minima':matched_minima,'even_minima':even_minima}


def prime_control(ep, sigma, slope_weight):
    p,y,b = 421,1024,Q(1000)
    a=y*b
    masks=[{0,1,2,4},{1,2,4,7}]
    m=2
    rows=[[orbit(8,T,p,a,b,Q(1),j,Q(15),Q(28),Q(8)) for j in range(1,m+1)]
          for T in masks]
    premiums=[sum(row['premium'] for row in r) for r in rows]
    tau=ep+m*sum(r[0]['tau_row'] for r in rows)
    io=2*sigma*max(map(ceil,premiums))
    total=sum(premiums)
    assert io<=2*sigma*(total+1)
    assert all(row['premium']>=b/4 for row in rows[0])
    net=total-tau-slope_weight*io
    return {'p':p,'bprime':str(b),'ep':str(ep),'sigma':str(sigma),
            'io_multiplier':str(slope_weight),'prime_premium':str(total),
            'tau':str(tau),'io':str(io),'net':str(net),
            'orbit_premiums':[str(x) for x in premiums],
            'orbit_rows':[[{k:str(v) for k,v in t.items()} for t in r] for r in rows]}


def main():
    yes=prime_control(Q(7),Q(1,50),Q(2))
    expensive=prime_control(Q(14000),Q(1,50),Q(2))
    assert Q(yes['net'])>0>Q(expensive['net'])
    assert yes['orbit_premiums']==expensive['orbit_premiums']
    print(json.dumps({'mask_census':[mask_census(n) for n in (4,8,16)],
                      'tent_census':tent_census(30720),'same_formula_controls':[yes,expensive]},indent=2))


if __name__=='__main__':
    main()
