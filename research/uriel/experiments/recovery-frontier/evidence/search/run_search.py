"""Rebuild and verify the sixteen-residue support/occupancy optimization."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import subprocess


@lru_cache(maxsize=None)
def exp_enclosure(t):
    term = F(1)
    total = term
    for k in range(1, 30):
        term = term*t/k
        total += term
    # Every later ratio is <=t/31. Remainder after degree 29 starts at degree 30.
    return total, total + term*t/30/(1-t/31)


def lt_exp(t, threshold):
    lo, hi = exp_enclosure(t)
    if lo == hi:
        return hi < threshold
    if lo < threshold <= hi:
        raise ValueError("Unresolved exponential comparison")
    return hi < threshold


def tables():
    records = []
    for size in [0,*range(7,17)]:
        for width in (2,4,8,16):
            upper = min(size,width) if size else 2*width
            rate = F(16,size) if size else F(1)
            for total in range(upper+1):
                for even in range(min(total, width//2 if size else width)+1):
                    mean = rate*total/width
                    even_mean = rate*even/width
                    empty = lt_exp(mean,F(10))
                    single = not total or (empty and lt_exp(mean,10*even_mean))
                    pair = not total or (empty and lt_exp(2*mean,100*even_mean))
                    records.append(f"{size} {width} {total} {even} {int(single)} {int(pair)}")
    return "\n".join(records)+"\n"


def translate(row):
    return dict(value=str(F(int(row[0]),int(row[1]))),support=int(row[2]),
                masses=list(map(int,row[3].split(","))))


def independent_score(orientation, support, masses):
    den, num = F(0), F(0)
    for t,mass in enumerate(masses):
        den += mass*F(1,32)
        for j in range(4):
            stride=2**j
            residue=t%stride
            nodenum=stride-1+residue
            even_child=(orientation>>nodenum)&1
            if (t//stride)%2 == even_child:
                continue
            den += mass*F(1,2*stride)
            orbit=[i for i in range(16) if i%stride==residue and support & (1<<i)]
            for shift in range(stride,16,2*stride):
                if all((i+shift)%16 not in orbit for i in orbit):
                    num += mass*F(1,16)
    return num/den if den else F(0)


def run():
    directory = Path(__file__).resolve().parent
    with TemporaryDirectory() as temp:
        exe=Path(temp)/"search"
        subprocess.run([os.getenv("CXX","c++"),"-std=c++17","-O2",
                        str(directory/"profile_search.cpp"),"-o",str(exe)],check=True)
        lines=subprocess.check_output([str(exe)],input=tables(),text=True).splitlines()
    reps,masks,profiles=map(int,lines[0].split())
    names=["equal_single","equal_pair","ternary_single","ternary_pair","cap_relaxation"]
    panels=[]
    for line in lines[1:]:
        fields=line.split()
        data=dict(orientation=int(fields[0]),multiplicity=int(fields[1]))
        for col,name in enumerate(names):
            item=translate(fields[2+4*col:6+4*col])
            assert independent_score(data["orientation"],item["support"],item["masses"])==F(item["value"])
            data[name]=item
        assert F(data["equal_single"]["value"])<=F(data["equal_pair"]["value"])
        assert F(data["ternary_single"]["value"])<=F(data["ternary_pair"]["value"])
        assert max(F(data[key]["value"]) for key in names[:-1])<=F(data["cap_relaxation"]["value"])
        panels.append(data)
    assert len(panels)==reps and sum(p["multiplicity"] for p in panels)==32768
    assert masks==8256 and profiles==119424
    answers={}
    for name in [*names,"best_certified"]:
        selected={p["orientation"]: (max((p[k] for k in names[:-1]),key=lambda y:F(y["value"]))
                                      if name=="best_certified" else p[name]) for p in panels}
        counts=Counter()
        for p in panels:
            counts[selected[p["orientation"]]["value"]]+=p["multiplicity"]
        weakest=min(selected,key=lambda z:F(selected[z]["value"]))
        largest=max(selected,key=lambda z:F(selected[z]["value"]))
        answers[name]=dict(minimax=selected[weakest]["value"],weakest_orientation=weakest,
                           weak_certificate=selected[weakest],maximum=selected[largest]["value"],
                           best_orientation=largest,orientation_histogram=dict(sorted(counts.items(),key=lambda x:F(x[0]))))
    return dict(orientation_classes=reps,orientations=32768,candidate_supports=masks,
                candidate_ternary_profiles=profiles,summary=answers,orbit_certificates=panels)


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    results=run()
    target=Path(__file__).with_name("results.json")
    certificates=results.pop("orbit_certificates")
    content=(json.dumps(results,indent=2)[:-1]+',"orbit_certificates":[\n' +
             ",\n".join(json.dumps(p,separators=(",",":")) for p in certificates) + "\n]}\n")
    if args.check:
        assert target.read_text()==content
    else:
        target.write_text(content)
    print(json.dumps({n:[v["minimax"],v["maximum"],v["weakest_orientation"]]
                      for n,v in results["summary"].items()}))


if __name__=="__main__":
    main()
