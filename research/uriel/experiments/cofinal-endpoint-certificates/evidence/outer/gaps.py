"""Exact checks of an every-outer-scale hitting lemma and an adversarial schedule."""
from fractions import Fraction as F
from itertools import product
import json


def band(U, J, c, w):
    assert U/J <= w <= U/2 and U >= 2*c
    return w,min(2*w,U-c)


def hits_closed(x, y):
    return max(x[0],y[0]) <= min(x[1],y[1])


def hits_open(band_, l, r):
    a,b=band_
    return a < r and b > l and (a<b or l<a<r)


def lerp(a,b,i,N):
    return (a*(N-i)+b*i)/N


def at_transition():
    total=0
    for J,c,v,t in product(map(F,("2","5/2","3","399/100","4")),
                           map(F,(0,1,7)),map(F,(7,16,31,100)),range(17)):
        U=2*v
        w=lerp(U/J,U/2,t,16)
        assert hits_closed(band(U,J,c,w),(v,v))
        total+=1
    # If the large-v qualification is dropped, the clipped band can be empty
    # even in the contiguous case. Use U fixed and a nonempty band example.
    v=F(6); c=F(7); J=F(4); U=2*v; w=U/J
    late_failure=w<=U-c<v
    assert late_failure
    return total,late_failure


def hitting_windows():
    equality=0
    strict=0
    for J,c,L,t in product(map(F,("401/100","5","8","31/2","200")),
                           map(F,(0,1,7)),map(F,(7,16,31,100)),range(17)):
        q=J/4; U=J*L/2
        w=lerp(U/J,U/2,t,16)
        assert hits_closed(band(U,J,c,w),(L,q*L))
        equality+=1
        for d in map(F,("1/100","1/4","3")):
            r=(q+d)*L
            U1=(J*L/2+2*r)/2
            w1=lerp(U1/J,U1/2,t,16)
            assert hits_open(band(U1,J,c,w1),L,r)
            strict+=1
    return equality,strict


def schedule(U,J,holes):
    if any(J*l/2<U<J*r for l,r in holes):
        return U/2
    return U/J


def multi(J, c, first, count):
    q=J/4
    L=first
    holes=[]
    for i in range(count):
        holes.append((L,q*L))
        L=(J*q+1)*L
    # Partition U by every branch switch or point where min(2w,U-c)
    # switches in the low schedule; band endpoints are affine on each part.
    # To audit all possible crossings of gap boundaries add equality cuts for
    # w=r and 2w=l for BOTH branches, and U-c=l for the clip.
    u0=max(F(1),2*c)
    u1=2*J*holes[-1][1]
    cuts={u0,u1}
    for l,r in holes:
        assert (J/2-1)*l>=c
        cuts.update([J*l/2,J*r,2*r,l,l+c])
    cuts.add(c/(1-2/J))
    cuts=sorted(x for x in cuts if u0<=x<=u1)
    probes=set(cuts)
    for a,b in zip(cuts,cuts[1:]):
        probes.add((a+b)/2)
    for U in probes:
        w=schedule(U,J,holes)
        seg=band(U,J,c,w)
        assert all(not hits_open(seg,l,r) for l,r in holes)
    for l,r in holes:
        low_edge=J*l/2
        high_edge=J*r
        assert hits_closed(band(low_edge,J,c,schedule(low_edge,J,holes)),(l,l))
        assert hits_closed(band(high_edge,J,c,schedule(high_edge,J,holes)),(r,r))
    return len(probes),len(holes),[(str(l),str(r)) for l,r in holes[:3]]


def sparse_counter():
    # Cofinal alone allows arbitrarily large multiplicative gaps even at J=2.
    U=F(4)
    rows=[]
    for _ in range(4):
        U2=U*U
        first=band(U,F(2),F(0),U/2);second=band(U2,F(2),F(0),U2/2)
        assert first[1]<second[0]
        rows.append(str(second[0]/first[1]))
        U=U2
    return rows


def run():
    a,b=at_transition()
    eq,st=hitting_windows()
    schedules=[]
    for J in map(F,("401/100","5","8","31/2","200")):
        n,h,illustrative=multi(J,F(7),F(16),5)
        schedules.append({"J":str(J),"q":str(J/4),"gaps":h,"cell_or_boundary_probes":n,
                          "first_three_open_gaps":illustrative})
    return {"covered_singletons":a,"late_clipping_needed_in_general":b,
            "closed_threshold_hits":eq,"strict_interior_hits":st,
            "sharp_schedules":schedules,
            "sparse_outer_control_J2_gap_ratios":sparse_counter()}


if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
