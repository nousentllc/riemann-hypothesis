"""Exact paired conditional sign test and conditional binomial interval."""
from math import comb

def prob_le(k,n,p):
    return sum(comb(n,i)*p**i*(1-p)**(n-i) for i in range(k+1))

def solve_decreasing(k,n,alpha):
    lo,hi=0.,1.
    for _ in range(70):
        mid=(lo+hi)/2
        if prob_le(k,n,mid)>alpha: lo=mid
        else: hi=mid
    return (lo+hi)/2

def paired(w,l):
    n=w+l
    if not n: return {'discordant':0,'two_sided_sign_p':1,'conditional_win_95pct':None}
    lower=0 if w==0 else solve_decreasing(w-1,n,.975)
    upper=1 if w==n else solve_decreasing(w,n,.025)
    return dict(discordant=n,two_sided_sign_p=min(1,2*prob_le(min(w,l),n,.5)),conditional_win_95pct=[lower,upper])
