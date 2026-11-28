"""The frozen policy with the literal prefactor, for one choice of rates across epsilon."""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"rates"))
from verify import HALF, tile_interval, sparse_anchor, endpoint, forms, groups, HARD, DELETIONS, dot
from verify import all_ordinary

def bisect_root(lo,hi,signed,unit,increasing):
    lo,hi=int(lo*unit),int(hi*unit)
    def below(k):
        lower,upper=signed(F(k,unit))
        assert lower>0 or upper<0
        return upper<0 if increasing else lower>0
    assert below(lo) and not below(hi)
    while hi-lo>1:
        k=(lo+hi)//2
        if below(k): lo=k
        else: hi=k
    return F(lo,unit),F(hi,unit)

def results():
    unit=10**12
    cl,cu=bisect_root(F(2392,1000),F(2393,1000),
                      lambda c:tile_interval(c,c/2,HALF),unit,False)
    # The positive small singleton root increases with c. Use separate outer endpoints.
    bl=bisect_root(F(7,10),F(71,100),lambda b:sparse_anchor(cl,b),unit,True)[0]
    bu=bisect_root(F(7,10),F(71,100),lambda b:sparse_anchor(cu,b),unit,True)[1]
    rate=(cl,bu,64-26*cl-bu)
    signatures=set()
    for ds in DELETIONS:
        signatures.update(forms(groups(HARD,True,True,ds)))
    extra=[]
    for total,even in sorted(signatures):
        mu,nu=dot(total,rate),dot(even,rate)
        if tile_interval(mu,nu)[0]<=0:
            assert (mu,nu)==(cl,cl/2)
            assert tile_interval(mu,nu,HALF)[0]>0 and nu*F(54,67)**2<1
            extra.append([str(mu),str(nu)])
    assert len(extra)==1 and endpoint(cu,bl)<all_ordinary()[1]
    return {"C_interval":list(map(str,(cl,cu))),"B_interval":list(map(str,(bl,bu))),
            "interior":list(map(str,rate)),"lower":str(endpoint(cl,bu)),"upper":str(endpoint(cu,bl)),
            "binding_forms":extra,"forms_checked":len(signatures)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args(); obj=results();out=HERE/"limit_corner.json"
    if args.write: out.write_text(json.dumps(obj,indent=2)+"\n")
    else: assert obj==json.loads(out.read_text())
    print(json.dumps(obj))

if __name__=="__main__":
    main()
