"""Exact cutoff projections and preassigned sparse families for the genuine slot-three filter."""
import json
from collections import Counter
from fractions import Fraction
from itertools import product

def next_power(z,p=3):
    m=1
    n=0
    while m<=z:
        m*=p
        n+=1
    return m,n

def exceptional(s,z):
    r=s%next_power(z)[0]
    return r if 1<=r<=z else 0

def bad(k,y2):
    # y2 is the square of the real ordinate. Endpoints must be retained.
    return k!=0 and k+1<=y2<k*k

def continuous_masks():
    """Each bit indexes an endpoint or an open cell between all change points."""
    grid=sorted({64,144}|{q for k in range(1,145) for q in (k+1,k*k) if 64<=q<=144})
    probes=sorted({Fraction(x) for x in grid}|{Fraction(x+y,2) for x,y in zip(grid,grid[1:])})
    masks={k:sum(1<<i for i,s in enumerate(probes) if bad(k,s)) for k in range(145)}
    return probes,masks

def compare_pairs():
    z1,z2=144,256
    p1,d1=next_power(z1);p2,d2=next_power(z2)
    probes,masks=continuous_masks()
    full=(1<<len(probes))-1
    old=[exceptional(s,z1) for s in range(p1)]
    new=[exceptional(s,z2) for s in range(p2)]
    panels={}
    for key,samples in (('common_center',((n%p1,n) for n in range(p2))),
                        ('unrelated_centers',product(range(p1),range(p2)))):
        stats=Counter()
        for i,j in samples:
            l=old[i];r=new[j]
            u=masks.get(l,0);v=masks.get(r,0)
            hole=u&v
            stats['tested']+=1
            stats['both_fail_entire_gap']+=hole==full
            stats['pointwise_two_record_cover']+=hole==0
            stats['at_least_one_missed_ordinate']+=bool(hole)
            if not bad(l,64) and not bad(r,144):
                stats['left_old_and_right_new_pass']+=1
                stats['passing_ends_with_two_record_hole']+=bool(hole)
                stats['passing_ends_later_alone_fills']+=v==0
            if key=='common_center':
                assert v&~u==0
                if r and r<=z1:assert r==l
        panels[key]=dict(stats)
    for z in (1,2,3,8,9,26,27,64,80,81,144,242,243,256):
        m,_=next_power(z)
        for s in range(m):
            e=exceptional(s,z)
            # Independent valuation characterization for three boundary queries plus representative.
            for n in {1,max(1,z-1),z,e or 1}:
                delta=s-n
                if delta:
                    v=0
                    while delta%3==0:
                        delta//=3;v+=1
                    seen=3**v>z
                else:seen=True
                assert (e==n)==(1<=n<=z and seen)
    return dict(gap=[8,12],cutoffs=[z1,z2],moduli=[p1,p2],digits=[d1,d2],
                event_probes=len(probes),panels=panels,
                whole_gap_danger=[k for k,v in masks.items() if v==full],
                some_gap_danger=[k for k,v in masks.items() if v!=0],
                compatible_lifts_of_thirteen=[dict(center=s,old=exceptional(s,z1),new=exceptional(s,z2))
                                             for s in (13,13+p1,13+2*p1)])

def source_scale():
    rows=[]
    for X in (12,16):
        Z=X**401;m,d=next_power(Z)
        eta=Fraction(1,128)
        assert 12 < 13**eta.denominator and 13+1<=8**401
        assert exceptional(13,Z)==13 and exceptional(0,Z)==0
        rows.append(dict(X=X,Z_power=f'{X}^401',strict_ternary_digits=d,
                         at_center_13=13,at_center_zero=0))
    z1,z2=12**401,16**401
    m1,d1=next_power(z1);m2,d2=next_power(z2)
    assert d2>d1 and exceptional(13+m1,z1)==13 and exceptional(13+m1,z2)==13+m1
    assert 13+m1>=12**401
    # The later label is outside all active cutoffs on the prescribed gap.
    return dict(Ct=401,eps='1/64',CK_assumed='>=1',upper_eta='1/128',rows=rows,
                added_digits=d2-d1,stable_old_label_lifts=f'1 out of 3^{d2-d1}',
                delayed_clearance_control='center 13+3^'+str(d1),
                effect='13 disappears at later cutoff; replacement exceeds active range')

def sparse_schedule():
    degrees=[2,4,16,256,65536,4294967296]
    assert all(b==a*a for a,b in zip(degrees,degrees[1:]))
    # Finite exact residue calculation at small degrees; symbolic integer-exponent comparisons at huge cases.
    prefix=sum(3**n for n in degrees[:4])
    exact=[]
    for j,n in enumerate(degrees[:3]):
        weight=sum(3**h for h in degrees[:j+1])
        late=degrees[j+1]
        assert prefix%3**late==weight and prefix%3**(late+1)!=weight
        assert 3**n<=weight<2*3**n
        exact.append(dict(n=n,weight=weight,last_matching_precision=late))
    thresholds=[]
    for J in (2,4,8,521,333632,10**9):
        n=2;j=1
        while n<=401*J:
            n=n*n;j+=1
        # Source Zmax=(3^n)^(401J). Divisibility is strict at the last admissible cutoff.
        assert n*n>401*J*n
        point_n=2
        point_j=1
        while 2*point_n<=3*401*J:
            point_n*=point_n;point_j+=1
        assert 2*point_n**2>3*401*J*point_n
        thresholds.append(dict(J=J,first_proved_index=j,log3_A=str(n),
                               first_pointwise_index=point_j,twice_pointwise_margin=str(2*point_n**2-3*401*J*point_n),
                               digit_margin=str(n*n-401*J*n)))
    return dict(schedule='n1=2; n(j+1)=n(j)^2; A(j)=3^n(j); [A(j),A(j)^(3/2)]',
                exact_small_prefix=exact,all_scale_cutoff_comparisons=thresholds)

if __name__=='__main__':
    print(json.dumps(dict(finite=compare_pairs(),source_scale=source_scale(),sparse=sparse_schedule()),indent=2))
