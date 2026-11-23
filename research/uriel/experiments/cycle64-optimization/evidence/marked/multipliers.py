"""Verify an adverse-label selector-aware rational dual. --search uses SciPy for proposals."""
import argparse
import json
import os
import subprocess
import tempfile
from fractions import Fraction as F
from pathlib import Path
from math import ceil

HERE=Path(__file__).resolve().parent
RATE_SCALE=1000
REWARD_SCALE=100000
CAP=2393
REM=1782


def facets(word):
    # Tangents to (999/100000) exp(2 mu). Round the positive factor down.
    result=[]
    for level in range(6):
        stride=1<<level
        for residue in range(stride):
            ev=(word>>(stride-1+residue))&1
            costs=[1 if t%stride==residue else 0 for t in range(64)]
            preferred=[int(t%(2*stride)==residue+ev*stride) for t in range(64)]
            # Optional positive intercepts are valid on the guaranteed path to the minimum.
            always=all((residue//s)%2==(word>>(s-1+residue%s))&1
                       for s in (1,2,4,8,16) if s<stride)
            tangencies=(0,1,2,3,4,5,6,7,8,9) if always else (2,3,4,5,6,7,8,9)
            for j in tangencies:
                u=F(j,4)
                term=total=F(1)
                for k in range(1,25):
                    term*=2*u/k
                    total+=term
                slope_base=F(int(total*F(999,100000)*10**6),10**6)
                w=64//stride
                intercept = w*slope_base*(2*u-1)
                coeff=[F(e) - 2*slope_base*i for e,i in zip(preferred,costs)]
                result.append((f"{stride}.{residue}.{j}",coeff,intercept))
    return result


def coefficients(word):
    den=[1]*64
    for t in range(64):
        for s in (1,2,4,8,16,32):
            c=t%s
            if ((t//s)&1) != ((word>>(s-1+c))&1):
                den[t]+=64//s
    return den


class Oracle:
    def __init__(self,exe,word):
        self.proc=subprocess.Popen([str(exe),str(word)],stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE,text=True)
    def query(self,z,price):
        self.proc.stdin.write(" ".join(map(str,[z,*price]))+"\n")
        self.proc.stdin.flush()
        line=self.proc.stdout.readline().split()
        if len(line)!=3:
            raise RuntimeError("Expected exact objective, full slots and partial slot")
        value,full,partial=map(int,line)
        assert full.bit_count()==26 and partial.bit_count()==1 and not full&partial
        masses=[CAP*((full>>t)&1)+REM*((partial>>t)&1) for t in range(64)]
        assert sum(masses)==64*RATE_SCALE
        return value,masses
    def close(self):
        self.proc.stdin.close()
        assert self.proc.wait()==0


def proposed_prices(rows,weights):
    v=[F(0)]*64
    constant=F(0)
    for key,cs,b in rows:
        lam=weights.get(key,0)
        if lam:
            for t in range(64):
                v[t]+=cs[t]*lam
            constant+=b*lam
    return [ceil(REWARD_SCALE*x) for x in v],ceil(RATE_SCALE*REWARD_SCALE*constant)


def trial(oracle,rows,den,z,weights):
    price,constant=proposed_prices(rows,weights)
    val,mass=oracle.query(z,price)
    q=sum(x*a for x,a in zip(den,mass))
    charged=sum(x*a for x,a in zip(price,mass))
    p,check=divmod(val+z*q-charged,REWARD_SCALE)
    assert check==0
    return val+constant,mass,p,q


def find(oracle,rows,den,max_iter):
    import numpy as np
    from scipy.optimize import linprog
    names=[f[0] for f in rows]
    matrix=np.array([[float(x) for x in cs] for _,cs,_ in rows])
    const=np.array([float(b) for _,_,b in rows])
    hist=[]; rhs=[]; weights={}; rho=.108
    best=(F(1),{})
    for step in range(max_iter):
        z=ceil(REWARD_SCALE*rho)
        gap,mass,p,q=trial(oracle,rows,den,z,weights)
        # At any mass allocation the denominator is at least 64*1000.
        upper=F(z,REWARD_SCALE)+F(max(0,gap),REWARD_SCALE*64*RATE_SCALE)
        if upper<best[0]:best=upper,weights.copy()
        hist.append(np.r_[-q/RATE_SCALE,matrix@np.array(mass)/RATE_SCALE+const])
        rhs.append(-p/RATE_SCALE)
        if gap<=0 and step>1: break
        result=linprog(np.r_[1.,np.zeros(len(rows))], A_ub=np.vstack(hist),
                       b_ub=np.array(rhs), bounds=[(.09,.3)]+[(0,2)]*len(rows),
                       method="highs-ds")
        if not result.success:raise RuntimeError(result.message)
        rho=float(result.x[0])+1.5e-5
        weights={n:F(round(x*10000),10000) for n,x in zip(names,result.x[1:]) if x>=.00005}
    # Discover the least tick accepted for these multipliers by the integer oracle.
    weights=best[1]
    lo,hi=10000,ceil(REWARD_SCALE*best[0])+2
    while lo+1<hi:
        mid=(lo+hi)//2
        if trial(oracle,rows,den,mid,weights)[0]<=0:hi=mid
        else:lo=mid
    gap,mass,p,q=trial(oracle,rows,den,hi,weights)
    assert gap<=0
    return dict(word=WORD,threshold=hi,denominator=REWARD_SCALE,adjusted_residual=gap,
                multipliers={k:str(v) for k,v in weights.items()},cuts=len(hist))


def verify(oracle,record):
    word=record["word"]; rows=facets(word); den=coefficients(word)
    assert (F(999,1000)**5190)<F(1,10)
    c=F(CAP,RATE_SCALE);term=total=F(1)
    for j in range(1,40):term*=2*c/j;total+=term
    assert total>50*c
    weights={k:F(v) for k,v in record["multipliers"].items()}
    assert set(weights)<=set(x[0] for x in rows) and all(x>=0 for x in weights.values())
    z=record["threshold"]
    gap,mass,p,q=trial(oracle,rows,den,z,weights)
    assert gap<=0 and gap==record["adjusted_residual"] and record["denominator"]==REWARD_SCALE
    previous=trial(oracle,rows,den,z-1,weights)[0]
    zero=trial(oracle,rows,den,z,{})[0]
    return {"upper":str(F(z,REWARD_SCALE)),"raw_zero_price_residual":zero,
            "accepted_residual":gap,"previous_tick_residual":previous,"active_cuts":len(weights)}


WORD=2556884934454963932
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--search",action="store_true")
    parser.add_argument("--iterations",type=int,default=140)
    parser.add_argument("--oracle",type=Path)
    parser.add_argument("--word",type=int,default=WORD)
    parser.add_argument("--output",type=Path,default=HERE/"certificate.json")
    args=parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        exe=args.oracle or Path(tmp)/"priced"
        if not args.oracle:
            subprocess.run([os.environ.get("CXX","c++"),"-std=c++17","-O3",
                            str(HERE/"priced.cpp"),"-o",str(exe)],check=True)
        record=None if args.search else json.loads(args.output.read_text())
        word=args.word if args.search else record["word"]
        oracle=Oracle(exe,word)
        try:
            if args.search:
                record=find(oracle,facets(word),coefficients(word),args.iterations)
                record["word"]=word
            checks=verify(oracle,record)
            if args.search:
                record["checks"]=checks
                args.output.write_text(json.dumps(record,indent=2)+"\n")
            else:assert checks==record["checks"]
            print(json.dumps(checks))
        finally:
            oracle.close()


if __name__=="__main__":
    main()
