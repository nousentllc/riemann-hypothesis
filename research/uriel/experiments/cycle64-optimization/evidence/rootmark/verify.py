"""Exact full-support upper bounds with a cap-detected marked-cell inequality."""
import argparse
from fractions import Fraction as F
from functools import cache
from importlib.util import module_from_spec, spec_from_file_location
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
RATE_SCALE = 10000
CAP = 23921
REST = 64*RATE_SCALE - 26*CAP
PRECISION = 10**7


def exp_lower(x):
    """Taylor partial sum at a nonnegative rational x."""
    assert x >= 0
    term = total = F(1)
    for k in range(1,40):
        term *= x/k
        total += term
    return total


def floor(x):
    return x.numerator//x.denominator


def ceil(x):
    return -floor(-x)


def preferred(word,s,c):
    return (word>>(s-1+c))&1


def cut(word,s,c,u,tip):
    """Zero-intercept activation for 0 <= u <= 1/2."""
    assert s in (1,2,4,8,16,32) and 0 <= c < s
    assert 0 <= u <= F(1,2) and tip%s==c
    k=F(floor(10**9*exp_lower(2*u)/100),10**9)
    coeff=[F(int(t%(2*s)==c+s*preferred(word,s,c))) - 2*k*int(t%s==c)
           for t in range(64)]
    coeff[tip] -= (1-2*u)*(64//s)*k/F(CAP,RATE_SCALE)
    return coeff


def node_data(word,support):
    den=[1]*64
    num=[0]*64
    groups=[]
    for s in (1,2,4,8,16,32):
        for c in range(s):
            sites=[t for t in support if t%s==c]
            if not sites:
                continue
            even=[t for t in sites if t%(2*s)==c+s*preferred(word,s,c)]
            odd=set(sites)-set(even)
            w=64//s
            missing=sum(all((t+s*h)%64 not in support for t in sites)
                        for h in range(1,w,2))
            for t in odd:
                num[t]+=2*missing
                den[t]+=w
            groups.append((sites,even,w))
    return num,den,groups


class Oracle:
    def __init__(self,exe,word):
        self.proc=subprocess.Popen([str(exe),str(word),str(PRECISION),str(CAP),str(RATE_SCALE),"2"],
                                   stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    def evaluate(self,z,adjust):
        assert all(isinstance(x,int) for x in adjust)
        self.proc.stdin.write(' '.join(map(str,[z,*adjust]))+'\n')
        self.proc.stdin.flush()
        res=self.proc.stdout.readline().split()
        if len(res)!=3:
            raise RuntimeError("support oracle returned an incomplete vertex")
        val,full,part=map(int,res)
        assert full.bit_count()==26 and part.bit_count()==1 and not(full&part)
        return val,full,part
    def close(self):
        self.proc.stdin.close()
        assert self.proc.wait()==0


def prices(word,settings):
    coeff=[F(0)]*64
    for spec in settings:
        s,c,u,tip,lam=spec
        lam=F(lam)
        assert lam>=0
        v=cut(word,s,c,F(u),tip)
        coeff=[x+lam*y for x,y in zip(coeff,v)]
    return [ceil(x*PRECISION) for x in coeff]


def closed_support(word,mask):
    sites={t for t in range(64) if mask>>t&1}
    for s in (1,2,4,8,16,32):
        for c in range(s):
            if any(t%s==c for t in sites):
                m=c
                for stride in (1,2,4,8,16,32):
                    if stride>=s:
                        m+=stride*preferred(word,stride,m)
                sites.add(m)
    return sites


def evaluate(exe,word,settings,write=False,threshold=None):
    adjust=prices(word,settings)
    oracle=Oracle(exe,word)
    try:
        @cache
        def val(z):
            return oracle.evaluate(z,adjust)
        if write:
            lo,hi=990000,1080000
            assert val(lo)[0]>0 and val(hi)[0]<=0
            while hi-lo>1:
                mid=(hi+lo)//2
                if val(mid)[0]>0:
                    lo=mid
                else:
                    hi=mid
            threshold=hi
        z=threshold
        r,caps,part=val(z)
        assert r<=0 and val(z-1)[0]>0
        raw=oracle.evaluate(z,[0]*64)[0]
        supp=closed_support(word,caps|part)
        num,den,_=node_data(word,supp)
        masses=[CAP*((caps>>t)&1)+REST*((part>>t)&1) for t in range(64)]
        physical=sum(m*(PRECISION*p-z*q+price) for m,p,q,price in zip(masses,num,den,adjust))
        # Removing zero mass geometric leaves can improve the gain. A strict increase here
        # would expose a larger legal oracle candidate with the same root-even count,
        # unless reevaluating a root-hole-free upper envelope created additional holes.
        return dict(word=word,settings=settings,threshold=z,scale=PRECISION,
                    bound=str(F(z,PRECISION)),residual=r,previous_tick=val(z-1)[0],
                    unpriced=raw,full_slots=caps,partial_slot=part,
                    minimal_closure=sorted(supp),closure_vertex_residual=physical)
    finally:
        oracle.close()


def check_lower(word,saved):
    spec=spec_from_file_location("frozen",HERE.parent/"rates"/"verify.py")
    frozen=module_from_spec(spec)
    spec.loader.exec_module(frozen)
    rates=[F(x) for x in saved["rates"]]
    assert len(rates)==64 and min(rates)>=0 and sum(rates)==64
    S={i for i,x in enumerate(rates) if x}
    num,den,groups=node_data(word,S)
    forms={(sum(rates[t] for t in sites)/w,sum(rates[t] for t in even)/w)
           for sites,even,w in groups}
    forms.update((a,a/2) for a in rates if a)
    assert all(nu>0 and frozen.tile_interval(mu,nu)[0]>0 for mu,nu in forms)
    p=sum(a*b for a,b in zip(rates,num))
    q=sum(a*b for a,b in zip(rates,den))
    return dict(ratio=str(p/q),percent=float(100*p/q),support=sorted(S),
                forms=len(forms))


def check_inputs():
    c=F(CAP,RATE_SCALE)
    assert exp_lower(2*c)>50*c
    assert F(64,100)*exp_lower(F(2))>F(472,100)>c
    assert 0<REST<CAP


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--oracle',type=Path)
    ap.add_argument('--record',type=Path,default=HERE/'certificate.json')
    ap.add_argument('--proposals',type=Path)
    args=ap.parse_args()
    check_inputs()
    with TemporaryDirectory() as tmp:
        exe=args.oracle or Path(tmp)/'priced'
        if not args.oracle:
            subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++17',
                            str(HERE.parent/'marked'/'priced.cpp'),'-o',str(exe)],check=True)
        if args.proposals:
            proposals=json.loads(args.proposals.read_text())
            rows=[evaluate(exe,r['word'],r['settings'],True) for r in proposals['uppers']]
            lower=proposals.get('word_specific_lower')
            if lower:lower['checks']=check_lower(lower['word'],lower)
            record={'rate_cap':str(F(CAP,RATE_SCALE)),'scale':PRECISION,
                    'uppers':rows,'word_specific_lower':lower}
            args.record.write_text(json.dumps(record,indent=2)+'\n')
        else:
            record=json.loads(args.record.read_text())
            assert record['rate_cap']==str(F(CAP,RATE_SCALE)) and record['scale']==PRECISION
            for r in record['uppers']:
                assert evaluate(exe,r['word'],r['settings'],threshold=r['threshold'])==r
            lower=record.get('word_specific_lower')
            if lower:assert lower['checks']==check_lower(lower['word'],lower)
        print([(r['word'],r['bound'],r['residual']) for r in record['uppers']])
        if lower:print(lower['checks'])


if __name__=='__main__':
    main()
