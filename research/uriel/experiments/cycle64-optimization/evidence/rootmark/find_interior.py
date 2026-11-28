"""Search a marked interior on a specified adverse labeling. SciPy only proposes rates."""
import argparse
import json
from pathlib import Path
from fractions import Fraction as F

import numpy as np
from scipy.optimize import minimize

from verify import HERE, Oracle, closed_support, node_data, check_lower, prices


def optimize(word, support):
    ids=sorted(support)
    if len(ids)*2.39208<64 or not ids:
        return
    p,q,groups=node_data(word,support)
    A=[]; B=[]
    for sites,even,width in groups:
        if not even:
            return
        A.append([int(t in sites)/width for t in ids])
        B.append([int(t in even)/width for t in ids])
    for t in ids:
        A.append([int(t==i) for i in ids])
        B.append([int(t==i)/2 for i in ids])
    A,B=np.array(A),np.array(B)
    p,q=np.array(p)[ids],np.array(q)[ids]
    def margins(x):
        mu,nu=A@x,B@x
        return np.log(10)-mu+np.minimum(.5*np.log(nu),5190/10381*np.log(nu))-2e-7
    def derivative(x):
        nu=B@x
        beta=np.where(nu>1,5190/10381,.5)
        return -A+(beta/nu)[:,None]*B
    def objective(x):
        return -(p@x)/(q@x)
    def gradient(x):
        return -p/(q@x)+(p@x)*q/(q@x)**2
    n=len(ids)
    cons=[dict(type='eq',fun=lambda x:sum(x)-64,jac=lambda x:np.ones(n)),
          dict(type='ineq',fun=margins,jac=derivative)]
    r=minimize(objective,np.full(n,64/n),jac=gradient,
               constraints=cons,method='SLSQP',bounds=[(.0209,2.392084)]*n,
               options={'maxiter':220,'ftol':1e-13})
    if min(margins(r.x))< -1e-8 or abs(sum(r.x)-64)>1e-8:
        return
    scale=10**8; z=np.floor(r.x*scale).astype(int)
    d=64*scale-sum(z)
    assert 0<=d<=len(z)
    z[np.argsort(-(r.x*scale-z))[:d]]+=1
    mass=[F(0)]*64
    for i,v in zip(ids,z):
        mass[i]=F(int(v),scale)
    return dict(word=word,rates=list(map(str,mass))),float(-objective(r.x))


def search(exe, word, settings, edits):
    o=Oracle(exe,word)
    seeds=set()
    try:
        for offset in (-.5,-.1,0,.1,.4):
            scaled=[[*row[:-1],str(max(F(0),F(row[-1])+F(str(offset))))] for row in settings]
            _,a,b=o.evaluate(1018300,prices(word,scaled))
            seeds.add(tuple(sorted(closed_support(word,a|b))))
    finally:
        o.close()
    supports=set(seeds)
    if edits:
        for seed in seeds:
            for t in range(64):
                mask=sum(1<<i for i in seed)^(1<<t)
                s=closed_support(word,mask)
                if len(s)>=27:
                    supports.add(tuple(sorted(s)))
    best=(-1,None)
    for active in sorted(supports):
        result=optimize(word,set(active))
        if result and result[1]>best[0]:
            best=result[1],result[0]
    if best[1]:
        print(json.dumps(dict(count=len(supports),exact=check_lower(word,best[1]))),flush=True)
    return best[1]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--record',type=Path,default=HERE/'certificate.json')
    ap.add_argument('--oracle',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--edits',action='store_true')
    a=ap.parse_args();r=json.loads(a.record.read_text())['uppers'][0]
    candidate=search(a.oracle,r['word'],r['settings'],a.edits)
    a.output.write_text(json.dumps(candidate,indent=2)+'\n')


if __name__=='__main__':
    main()
