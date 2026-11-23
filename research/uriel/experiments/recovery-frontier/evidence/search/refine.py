"""Hunt continuous profiles and independently certify rational witnesses."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from math import exp, floor
from run_search import independent_score, lt_exp


def rows(ori,support):
    active=[i for i in range(16) if support & (1<<i)]
    total,evens,k,r=[],[],[],[]
    for j in range(4):
        s=1<<j
        for c in range(s):
            child=(ori>>(s-1+c))&1
            allmask=[F(s,16) if i%s==c else F(0) for i in active]
            if not any(allmask):
                continue
            evenmask=[a if (i//s)%2==child else F(0) for a,i in zip(allmask,active)]
            total.append(allmask);evens.append(evenmask)
    for i in active:
        total.append([F(int(i==a)) for a in active])
        evens.append([F(int(i==a),2) for a in active])
    for i in active:
        den=1;num=0
        for j in range(4):
            s=1<<j;c=i%s
            if (i//s)%2==(ori>>(s-1+c))&1:
                continue
            den+=16//s
            for h in range(s,16,2*s):
                if not any((t+h)%16 in active for t in active if t%s==c):
                    num+=2
        r.append(num);k.append(den)
    return active,total,evens,k,r


def certificate(ori,mask,z,info):
    active,total,evens,_,_=info
    flat=[F(0)]*16
    for i,v in zip(active,z):
        flat[i]=v
    if sum(z)!=16 or min(z)<=0 or max(z)>F(23,10):
        return None
    for a,b in zip(total,evens):
        mu=sum(x*y for x,y in zip(z,a)); me=sum(x*y for x,y in zip(z,b))
        if not lt_exp(mu,F(10)) or not lt_exp(2*mu,100*me):
            return None
    ratio=independent_score(ori,mask,flat)
    return dict(value=str(ratio),support=mask,rates=[str(v) for v in flat])


def attempt(ori,mask):
    info=rows(ori,mask)
    active,aa,bb,k,r=info
    A=[[float(v) for v in row] for row in aa]
    B=[[float(v) for v in row] for row in bb]
    n=len(active)
    dot=lambda a,b:sum(i*j for i,j in zip(a,b))
    x=[16/n]*n
    def feasible(vec):
        return all(dot(bb,vec) >= .01*exp(2*dot(aa,vec))+1e-7 for aa,bb in zip(A,B))
    if not feasible(x):
        return None
    # Move mass along useful pair transfers. Convexity of the feasibility
    # region makes the feasible segment from the incumbent an interval.
    for _ in range(180):
        ratio=dot(r,x)/dot(k,x)
        linear=[v-ratio*z for v,z in zip(r,k)]
        best=None
        for i in range(n):
            for j in range(n):
                if x[i]<=1e-6 or 2.3-x[j]<=1e-9 or linear[j]-linear[i]<=1e-9:continue
                lo,hi=0.0,min(x[i]-1e-6,2.3-x[j]); probe=x[:]
                for _ in range(30):
                    mid=(lo+hi)/2
                    probe[i]=x[i]-mid;probe[j]=x[j]+mid
                    if feasible(probe):lo=mid
                    else:hi=mid
                gain=lo*(linear[j]-linear[i])
                if best is None or gain>best[0]:best=(gain,lo,i,j)
        if best is None or best[0]<1e-9:break
        _,v,i,j=best;x[i]-=v;x[j]+=v
    denom=10**7
    raw=[floor(v*denom+1e-8) for v in x]
    for i in sorted(range(n),key=lambda i:raw[i]-x[i]*denom):
        if sum(raw)==16*denom:break
        if raw[i]<23*denom//10:raw[i]+=1
    return certificate(ori,mask,[F(int(a),denom) for a in raw],info)


def run():
    src=json.loads(Path(__file__).with_name("results.json").read_text())
    survivors=[]; overall=F(1)
    for row in src["orbit_certificates"]:
        best=max((row[k] for k in ("equal_single","equal_pair","ternary_single","ternary_pair")),
                 key=lambda z:F(z["value"]))
        if F(best["value"])>=F(23,348):
            overall=min(overall,F(best["value"]))
            continue
        masks={best["support"],row["cap_relaxation"]["support"]}
        found=[v for mask in sorted(masks) if (v:=attempt(row["orientation"],mask)) is not None]
        candidate=max([best,*found],key=lambda z:F(z["value"]))
        survivors.append(dict(orientation=row["orientation"],multiplicity=row["multiplicity"],
                              presearch=best["value"],strongest=candidate))
        overall=min(overall,F(candidate["value"]))
    return dict(minimax_lower=str(overall),orientation_upper="23/348",
                excess_upper=str(F(23,348)-overall),improvement_panels=survivors)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    file=Path(__file__).with_name("refinement.json")
    if args.check:
        saved=json.loads(file.read_text())
        primary=json.loads(Path(__file__).with_name("results.json").read_text())
        known={r["orientation"]:max(F(r[k]["value"]) for k in ("equal_single","equal_pair","ternary_single","ternary_pair"))
               for r in primary["orbit_certificates"]}
        for p in saved["improvement_panels"]:
            o=p["orientation"]; v=p["strongest"];active,*_=rows(o,v["support"])
            if "rates" in v:
                info=rows(o,v["support"])
                assert certificate(o,v["support"],[F(v["rates"][i]) for i in active],info)==v
            else:
                assert F(v["value"])==known[o]
            known[o]=max(known[o],F(v["value"]))
        assert min(known.values())==F(saved["minimax_lower"])
        result=saved
    else:
        result=run(); file.write_text(json.dumps(result,indent=2)+"\n")
    print({k:v for k,v in result.items() if k!="improvement_panels"})
    print([(row["orientation"],row["strongest"]["value"]) for row in result["improvement_panels"]])


if __name__=="__main__":
    main()
