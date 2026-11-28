"""Continuous delayed-pole control, standard library only."""
import json
from math import exp,expm1,log
def run():
    T=log(8192);beta=.75;theta=.5;eta=.1
    rows=[]
    for ratio in (.25,.5,2/3,1.,1.5,2.,3.,4.,6.):
        U=ratio*T;V=1.5*U;lo=max(T,U)
        if V<=lo: mass=check=0.
        else:
            length=V-lo
            mass=exp(-theta*lo)*(exp(beta*(lo-T))*expm1((beta-theta)*length)/(beta-theta)
                 -exp(-(lo-T))*expm1((-1-theta)*length)/(-1-theta))
            def f(u):return exp(-theta*u)*(exp(beta*(u-T))-exp(-(u-T)))
            n=4096;step=length/n
            check=step/3*(f(lo)+f(V)+sum((4 if i%2 else 2)*f(lo+step*i) for i in range(1,n)))
            assert abs(mass-check)<5e-10*max(mass,1e-25)
        rows.append(dict(U_over_T=ratio,mass=mass,cap=exp(eta*U),cap_exceeded=mass>exp(eta*U)))
    assert rows[1]['mass']==0 and rows[-1]['cap_exceeded']
    res=exp(-beta*T)
    return dict(T=T,residue=res,rows=rows,eta=eta,first_observed_crossover=next(r['U_over_T'] for r in rows if r['cap_exceeded']))
if __name__=='__main__':print(json.dumps(run(),indent=2))

