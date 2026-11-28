"""A rational envelope and worked instances of the epsilon-dependent minimax formula."""
import argparse
from fractions import Fraction as F
from math import ceil
import json
from pathlib import Path
from limit_corner import bisect_root, forms, groups, HARD, DELETIONS, dot, endpoint
from verify import HALF, BETA, logarithm, tile_interval, sparse_anchor, all_ordinary

HERE = Path(__file__).resolve().parent

def at(epsilon):
    r=ceil(32/epsilon+64)+1
    n=6*r+1
    beta=F(3*r,n)
    h=2+8*epsilon
    k=(h+2)/(h+3)
    loglo,loghi=logarithm(k)
    def margin(mu,nu):
        lo,hi=tile_interval(mu,nu,beta)
        return lo-loghi/n, hi-loglo/n
    unit=10**12
    cl,cu=bisect_root(F('2.39208'),F('2.39213'),lambda c:margin(c,c/2),unit,False)
    bl=bisect_root(F('.7058'),F('.7064'),lambda b:margin((b+5*cl)/32,b/32),unit,True)[0]
    bu=bisect_root(F('.7058'),F('.7064'),lambda b:margin((b+5*cu)/32,b/32),unit,True)[1]
    return dict(epsilon=str(epsilon),r=r,cap=[str(cl),str(cu)],singleton=[str(bl),str(bu)],
                lower=str(endpoint(cl,bu)),upper=str(endpoint(cu,bl)))

def run():
    cl,cu,bl,bu=map(F,['2.39208','2.39213','.7058','.7064'])
    floor=logarithm(F(4,5))[0]/10381
    assert tile_interval(cl,cl/2,BETA)[0]>0
    assert tile_interval(cu,cu/2,HALF)[1]<floor
    assert tile_interval(F(1),cu/64,BETA)[1]<floor
    assert sparse_anchor(cl,bl,BETA)[1]<floor
    assert sparse_anchor(cu,bu,HALF)[0]>0
    assert bu/(32*BETA-bu)<F(1,15)
    signatures=set()
    for ds in DELETIONS:
        signatures.update(forms(groups(HARD,True,True,ds)))
    special={((1,0,0),(HALF,0,0)),((F(5,32),F(1,32),0),(0,F(1,32),0))}
    low=(cl,bl,64-26*cu-bu); high=(cu,bu,64-26*cl-bl)
    slack=min(tile_interval(dot(mu,high),dot(nu,low))[0] for mu,nu in signatures-special)
    assert slack>F(14,100) and endpoint(cu,bl)<all_ordinary()[1]
    assert F(10118,100000)<endpoint(cl,bu)
    return {"cap_range":[str(cl),str(cu)],"singleton_range":[str(bl),str(bu)],
            "remaining_standard_log_slack_exceeds":"7/50","nonbinding_forms":len(signatures-special),
            "uniform_outer":str(endpoint(cu,bl)),
            "instances":[at(e) for e in [F(64,3329),F(1,64),F(1,256),F(1,1024)]]}

def main():
    p=argparse.ArgumentParser();p.add_argument("--write",action="store_true")
    args=p.parse_args(); data=run();out=HERE/"exponent.json"
    if args.write:out.write_text(json.dumps(data,indent=2)+"\n")
    else: assert data==json.loads(out.read_text())
    print("fixed-epsilon checks",[(d["epsilon"],100*float(F(d["lower"]))) for d in data["instances"]])

if __name__=="__main__":
    main()
