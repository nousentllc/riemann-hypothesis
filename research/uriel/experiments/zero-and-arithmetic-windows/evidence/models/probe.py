"""Finite controls for a one-sided multiplicative-power window. Python standard library.
Primary quantities are evaluated after scaling by the terminal exponential.
Save a machine-readable record with python3 -B probe.py > results.json.
"""
from __future__ import annotations
import cmath
import json
import math
from math import exp, log, sin, cos, pi

def periodic(phase,a,w):
    """Normalized infinite-past integral at terminal phase, for a>0."""
    t=(phase+pi/2)%(2*pi)
    den=a*a+w*w
    half=exp(-a*pi/w)
    if t>=pi:
        return w/(den*(1-half))*exp(-a*(t-pi)/w)
    x=t-pi/2
    return (a*cos(x)+w*sin(x)+w*exp(-a*t/w)/(1-half))/den

def window_mass(psi,L,a,w):
    """Independent integration of the intersection of every positive lobe with [-L,0]."""
    bend=math.ceil((psi+pi/2)/(2*pi))+1
    start=math.floor((psi-w*L-pi/2)/(2*pi))-1
    total=[]
    def primitive(t):
        return exp(a*t)*(a*cos(psi+w*t)+w*sin(psi+w*t))/(a*a+w*w)
    for j in range(start,bend+1):
        lo=max(-L,(-pi/2+2*pi*j-psi)/w)
        hi=min(0,(pi/2+2*pi*j-psi)/w)
        if hi>lo:total.append(primitive(hi)-primitive(lo))
    return math.fsum(total)

def root_extreme(a,w,maximize):
    lo,hi=(0,pi/2) if maximize else (-pi/2,0)
    for _ in range(65):
        m=(lo+hi)/2
        d=max(0,cos(m))-a*periodic(m,a,w)
        if (d>0)==maximize:lo=m
        else:hi=m
    phase=(lo+hi)/2
    return phase,periodic(phase,a,w)

def phase_sweep():
    w=2.;a=.25;d=.5
    ps,hmin=root_extreme(a,w,False);pt,hmax=root_extreme(a,w,True)
    rows=[];worst=0
    for U in (4,8,16,32,64,128,256):
        L=d*U; end=(1+d)*U
        vals=[]
        phases=[2*pi*j/256 for j in range(256)]+[ps,pt]
        for psi in phases:
            v=window_mass(psi,L,a,w)
            other=periodic(psi,a,w)-exp(-a*L)*periodic(psi-w*L,a,w)
            worst=max(worst,abs(other-v))
            assert abs(other-v)<2e-12
            assert v>=hmin-exp(-a*L)*hmax-3e-13
            vals.append(v)
        # Set the real part of the finite untruncated integral to zero.
        D=(1-cmath.exp(-(a+1j*w)*L))/(a+1j*w)
        signed_phase=pi/2-cmath.phase(D)
        signed=(cmath.exp(1j*signed_phase)*D).real
        on_signed_zero=window_mass(signed_phase,L,a,w)
        assert abs(signed)<1e-13 and on_signed_zero>0
        rows.append(dict(U=U,scaled_min_sample=min(vals),scaled_max_sample=max(vals),
            scaled_uniform_lower=max(0,hmin-exp(-a*L)*hmax),
            scaled_uniform_upper=hmax,log_min_sample_over_U=log(min(vals))/U+a*end/U,
            signed_zero_abs=abs(signed),scaled_mass_at_signed_zero=on_signed_zero))
    late=rows[-1]
    assert abs(late['log_min_sample_over_U']-.375)<.004
    exact_zeros=window_mass(pi,pi/(4*w),a,w)
    assert exact_zeros==0
    return dict(phase_min=ps,min_H=hmin,phase_max=pt,max_H=hmax,lobe_primitive_max_abs_difference=worst,
            rows=rows,fixed_log_width_negative_lobe_mass=exact_zeros)

def powers():
    rows=[]
    for U in (4,8,16,32,64):
        L=U/2
        for gap in (-.125,0,.25):
            m=exp(gap*U)*math.expm1(gap*L)/gap if gap else L
            # Sign change of the real residue makes all positive mass vanish.
            rows.append(dict(U=U,gap=gap,positive_mass=m,negative_residue_mass=0))
    # Both endpoints at negative minima, with a full positive lobe in between.
    w=2.;L=2*pi/w
    z=window_mass(pi,L,.25,w)
    assert z>0 and cos(pi-w*L)<0 and cos(pi)<0
    return dict(rows=rows,endpoint_test=dict(left=-1,right=-1,scaled_positive_mass=z))

def derivatives():
    s=4.;theta=.5;beta=.75;w=2.;E=s-theta
    def coefficient(t,k):
        return .5/E*((E/(s-beta+1j*(t-w)))**(k+1)+(E/(s-beta+1j*(t+w)))**(k+1))
    def polar(t,k):
        out=0j
        for v in (t-w,t+w):
            A=E/math.hypot(s-beta,v);angle=-(k+1)*math.atan2(v,s-beta)
            out+=.5/E*A**(k+1)*complex(cos(angle),sin(angle))
        return out
    rows=[]
    for k in (4,8,16,32,64,128,256,512):
        f0=coefficient(0,k);fw=coefficient(w,k)
        assert all(abs(coefficient(t,k)-polar(t,k))<1e-11*max(1,abs(coefficient(t,k))) for t in (0,w))
        comb=abs(fw)+f0.real
        rows.append(dict(order=k,scaled_real=f0.real,scaled_shift_abs=abs(fw),scaled_one_sided=comb,
              log_rate=log(comb)/k if comb>0 else None))
    assert abs(rows[-1]['log_rate']-log(E/(s-beta)))<.005
    return dict(sigma=s,theta=theta,beta=beta,frequency=w,predicted_limit=log(E/(s-beta)),rows=rows,
                negative_real_residue_combination_at_t_zero=0)

def logpoisson(mu,k,tail_up):
    """Log of one decreasing Poisson tail, including term k; no subtraction of nearly equal CDFs."""
    assert k>=mu if tail_up else k<=mu
    totals=[1.];j=k;t=1.
    while True:
        if tail_up:j+=1;t*=mu/j
        elif j>0:t*=j/mu;j-=1
        else:break
        totals.append(t)
        if t<1e-19:break
    return -mu+k*log(mu)-math.lgamma(k+1)+log(math.fsum(totals))

def localization():
    rows=[]
    for U in (2,4,8,16,32,64,128):
        s=64.;k=math.ceil(1.25*s*U)
        for r in (s,s-2):
            shape=k+1;args=(r*U,r*1.5*U)
            left=logpoisson(args[0],shape,True)
            right=logpoisson(args[1],k,False)
            for z,v in zip(args,(left,right)):
                x=z/shape;assert v<=-shape*(x-1-log(x))+1e-9
            rows.append(dict(U=U,k=k,rate=r,left_log10=left/log(10),right_log10=right/log(10)))
    return rows

def area_tri(t):
    if t<=-1:return 0.
    if t<0:return (t+1)**2/2
    if t<1:return 1-(1-t)**2/2
    return 1.

def comb(U,V,h,b,c=.125):
    pieces=[]; peak=0;lower=0;upper=0
    for n in range(max(1,math.floor(U)-1),math.ceil(V)+2):
        w=c*exp(-b*n)
        # Subtract integer centers before division, even when adding width to n would round to n.
        u=(U-n)/w;v=(V-n)/w
        frac=area_tri(v)-area_tri(u)
        if frac:
            mass=c*exp((h-b)*n)
            pieces.append(mass*frac)
            z=0 if u<=0<=v else min(abs(u),abs(v))
            peak=max(peak,exp(h*n)*max(0,1-z))
            if u<=-1 and v>=1:lower+=mass
            upper+=mass
    exact=math.fsum(pieces)
    assert lower-1e-12*max(lower,1)<=exact<=upper+1e-12*max(upper,1)
    return exact,peak

def tri_transform(z):
    # Series for 2(cosh(z)-1)/z^2, including removable value at zero.
    t=1.;sm=t
    for j in range(1,15):
        t*=z*z/((2*j+1)*(2*j+2));sm+=t
    return sm

def spike_sweep():
    h=.25;theta=.5;c=.125
    records=[]
    for b in (.125,.25,.5):
        rows=[]
        for U0 in (4,8,16,32,64,128):
            for offset in (0.,.375):
                U=U0+offset;V=1.5*U
                m,p=comb(U,V,h,b)
                rows.append(dict(U=U,mass=m,normalized_peak=p,log_mass_over_U=log(m)/U))
        beta=theta+h-b
        check=[]
        for eps in (.25,.0625,.015625,.00390625):
            s=beta+eps
            # Sum in two ways: center-geometric plus rapidly converging width correction, vs direct  explicit truncation.
            M=math.ceil(38/eps)
            direct=math.fsum(c*exp(-eps*n)*tri_transform((s-theta)*c*exp(-b*n)) for n in range(1,M+1))
            const=0.
            for n in range(1,300):
                z=(s-theta)*c*exp(-b*n)
                const+=c*exp(-eps*n)*(tri_transform(z)-1)
            full=c/math.expm1(eps)+const
            assert abs(direct-full)<1e-12*max(1,full)
            check.append(dict(epsilon=eps,scaled_transform=eps*full,truncation_absolute_diff=abs(direct-full)))
        assert abs(check[-1]['scaled_transform']-c)<.0003
        records.append(dict(width_exponent=b,rightmost_pole=beta,real_residue=c,rows=rows,transform_checks=check))
    return records

def run():
    return dict(oscillatory=phase_sweep(),real=powers(),derivative=derivatives(),kernel=localization(),spikes=spike_sweep())
if __name__=='__main__':
    if not __debug__:raise SystemExit("Run without -O to enable controls.")
    print(json.dumps(run(),indent=2,sort_keys=True))

