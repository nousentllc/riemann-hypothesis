"""Post-hoc continuous antiderivative cross-check for the six nonprincipal rows.
The prime-power enumeration and integration differ from prime_mass.py. The
rigorous elementary log and power primitives and the c4 certificate are shared.
"""
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path
from prime_mass import I,S,ZERO,beta_constants,box,log,pow_theta


def factors(limit):
    events=[]
    for n in range(3,limit+1,2):
        p=next((r for r in range(3,isqrt(n)+1,2) if not n%r),n)
        q=n
        while not q%p:q//=p
        if q==1:events.append((n,p))
    return events


def mass_affine(a,b,x,y,j):
    """Enclose positive mass and logarithmic length of the set ay-b>0."""
    t=F(j,4)
    gx,gy=a*x-b,a*y-b
    if max(gx,gy)<=0:return ZERO,ZERO
    if min(gx,gy)<0:
        cut=b/a
        assert x<cut<y
        if gx<0:x=cut
        else:y=cut
    def prim(v):
        iv=pow_theta(v,j).reciprocal()
        return iv.scale((a*v)/(1-t)+b/t)
    return prim(y)-prim(x),log(F(y)/x)


def row(Y,j,c4):
    events=factors(Y*isqrt(Y))
    stops=[Y]+[n for n,p in events if Y<n<Y*isqrt(Y)]+[Y*isqrt(Y)]
    a,b=c4,ZERO
    mass=occupied=ZERO
    scores={}
    def advance(n,p):
        lm=log(p).scale(1 if n%4==1 else -1)
        return lm.scale(F(1,n)),lm
    for n,p in events:
        if n>Y:break
        a0,b0=advance(n,p);a=a+a0;b=b+b0
    weights=dict(events)
    for x,y in zip(stops,stops[1:]):
        lo,llo=mass_affine(F(a.lo,S),F(b.hi,S),F(x),F(y),j)
        hi,lhi=mass_affine(F(a.hi,S),F(b.lo,S),F(x),F(y),j)
        mass=mass+I(max(0,lo.lo),hi.hi)
        occupied=occupied+I(llo.lo,lhi.hi)
        scores[x]=(a.scale(x)-b)*pow_theta(F(x),j).reciprocal()
        scores[y]=(a.scale(y)-b)*pow_theta(F(y),j).reciprocal()
        if y in weights:
            aa,bb=advance(y,weights[y]);a=a+aa;b=b+bb
    floor=max(z.lo for z in scores.values());ceiling=max(z.hi for z in scores.values())
    assert floor>0
    peak=I(floor,ceiling)
    winners=[x for x,z in scores.items() if z.hi>=floor]
    window_width=log(isqrt(Y))
    ratio=mass*(peak*window_width).reciprocal()
    support=occupied*window_width.reciprocal()
    conditional=mass*(occupied*peak).reciprocal()
    return dict(Y=Y,theta=str(F(j,4)),peak=peak.pair(12),mass=mass.pair(12),
                knots=len(stops),argmax_candidates=winners,ratio=ratio.pair(12),log_support_fraction=support.pair(12),
                mean_positive_height_over_peak=conditional.pair(12))


def run():
    d=Path(__file__).resolve().parent
    primary=json.loads((d/'results.json').read_text())
    c4,_=beta_constants()
    rows=[]
    by_key={(r['Y'],r['theta']):r for r in primary['rows'] if r['character']=='chi4'}
    for Y in (16,64,256):
        for j in (2,3):
            s=row(Y,j,c4)
            ref=by_key[(Y,s['theta'])]
            for k in ('mass','peak','ratio'):
                l,r=map(F,ref[k]);ll,rr=map(F,s[k])
                assert l<=ll<=rr<=r
            assert len(s['argmax_candidates'])==1
            rows.append(s)
    return dict(method='analytic clipped-affine primitive with outward rounding',rows=rows)


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
