"""Discover a one-node price from exact oracle vertices with a two-variable exchange."""
import argparse
from fractions import Fraction as F
from pathlib import Path

from verify import (CAP, PRECISION, RATE_SCALE, REST, Oracle, ceil, cut, preferred)


def fit(lines):
    """Minimize the maximum of finitely many affine functions on [0,2]."""
    candidates={F(0),F(2)}
    for i,(a,b) in enumerate(lines):
        for c,d in lines[:i]:
            if b!=d:
                x=(c-a)/(b-d)
                if 0<x<2:
                    candidates.add(x)
    def cost(x):
        return max(a+b*x for a,b in lines)
    return min((cost(x),x) for x in candidates)


def discover(exe,word,tip,u):
    C=cut(word,2,1,u,tip)
    den=[1+sum((64//s) for s in (1,2,4,8,16,32)
               if (t//s)%2!=preferred(word,s,t%s)) for t in range(64)]
    lines=[]; seen=set(); z0,lam=F(102,1000),F(0)
    oracle=Oracle(exe,word)
    try:
        for _ in range(25):
            z=ceil(z0*PRECISION)
            adjust=[ceil(x*lam*PRECISION) for x in C]
            score,mask,part=oracle.evaluate(z,adjust)
            masses=[CAP*((mask>>t)&1)+REST*((part>>t)&1) for t in range(64)]
            q=sum(a*b for a,b in zip(masses,den))
            p,check=divmod(score+z*q-sum(a*b for a,b in zip(masses,adjust)),PRECISION)
            assert check==0
            line=(F(p,q),sum(a*b for a,b in zip(masses,C))/q)
            if line in seen:
                break
            seen.add(line);lines.append(line)
            z0,lam=fit(lines)
        z=ceil(z0*PRECISION)
        adjust=[ceil(x*lam*PRECISION) for x in C]
        while oracle.evaluate(z,adjust)[0]>0:
            z+=1
    finally:
        oracle.close()
    return len(lines),lam,z


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oracle',type=Path,required=True)
    parser.add_argument('--word',type=int,default=2549776587809433532)
    parser.add_argument('--tip',type=int,default=9)
    parser.add_argument('--tangent',type=F,default=F(3,8))
    args=parser.parse_args()
    count,lam,z=discover(args.oracle,args.word,args.tip,args.tangent)
    print('separating vertices',count,'price',lam,'upper',F(z,PRECISION))


if __name__=='__main__':
    main()
