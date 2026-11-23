"""List all supports attaining positive unpriced surplus, then remove them and optimize again."""
import argparse
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
WORD = 2549776587809433532
EXCLUDED = (1230983613671479063,1518083709116552983)
TOP, BOTTOM = 10118, 100000


def execute(executable, fields):
    return subprocess.check_output([executable],text=True,input=" ".join(map(str,fields))+"\n").splitlines()


def transport(word):
    def order(c, stride):
        if stride == 64:
            return [c]
        child = (word >> (stride-1+c)) & 1
        return order(c+stride*child,2*stride)+order(c+stride*(1-child),2*stride)
    sequence = order(0,1)
    mapped = [2*((11*(t//2)+6)%32)+1 if t%2 else t for t in sequence]
    rank = {t:i for i,t in enumerate(mapped)}
    result = 0
    for stride in (1,2,4,8,16,32):
        for c in range(stride):
            anchor = min(range(c,64,stride),key=rank.get)
            result |= ((anchor//stride)%2) << (stride-1+c)
    return result


def phase_control(executable):
    seed = 7382425669205845932
    assert transport(seed) == WORD
    rows=[]
    for word, top, bottom in ((seed,32,187),(WORD,58,567)):
        raw = subprocess.check_output([executable,str(word),str(bottom),"12","5","2"],
                                      input=" ".join(map(str,[top,*([0]*64)]))+"\n",text=True)
        maximum,full,partial=map(int,raw.split())
        assert maximum==0 and full.bit_count()==26 and partial.bit_count()==1 and not (full&partial)
        rows.append({"word":word,"closed_box_ratio":f"{top}/{bottom}","maximum_surplus":maximum})
    return rows


def verify():
    rows = []
    with TemporaryDirectory() as folder:
        near = Path(folder)/"near"
        puncture = Path(folder)/"puncture"
        for binary in (near,puncture):
            subprocess.run([os.environ.get("CXX","c++"),"-O3","-std=c++17",
                            HERE/(binary.name+".cpp"),"-o",binary],check=True)
        priced = Path(folder)/"priced"
        subprocess.run([os.environ.get("CXX","c++"),"-O3","-std=c++17",
                        HERE.parent/"marked"/"priced.cpp","-o",priced],check=True)
        phase = phase_control(priced)
        for full,unit in ((23921,10000),(239213,100000)):
            partial = 64*unit - 26*full
            fields = [WORD,TOP,BOTTOM,full,partial]
            splits, supports = [], {}
            rooted, raw, distinct = None, None, None
            for line in execute(near,fields):
                label,*data = line.split()
                values = list(map(int,data))
                if label == "root":
                    rooted,raw,distinct = values
                elif label == "split":
                    slots,owns_partial,left,right,pairs = values
                    splits.append(dict(even_full=slots,even_partial=owns_partial,
                                       even_masks=left,odd_masks=right,positive_pairs=pairs))
                elif label == "support":
                    mask,excess = values
                    assert mask not in supports and excess>0
                    supports[str(mask)] = excess
                else:
                    raise ValueError(line)
            assert rooted < 0 and (raw,distinct)==(42384,39058)
            assert set(map(int,supports))==set(EXCLUDED)
            assert splits==[dict(even_full=21,even_partial=1,even_masks=2,odd_masks=1,positive_pairs=2)]
            remaining, witness = map(int,execute(puncture,[*fields,*EXCLUDED])[0].split())
            assert remaining < 0 and witness not in EXCLUDED
            rows.append({"rate_cap":f"{full}/{unit}","rate_unit_denominator":unit,
                         "root_hole":rooted,"root_pairs":raw,"distinct_root_supports":distinct,
                         "positive_splits":splits,"positive_uncredited_support_surpluses":supports,
                         "best_other_uncredited":remaining,"other_witness":str(witness)})
    return {"word":WORD,"threshold_numerator":TOP,"threshold_denominator":BOTTOM,
            "integer_units":"rate unit denominator times threshold denominator",
            "legal_half_masks_each":3263443,"phase_control":phase,"censuses":rows}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    result=verify()
    dest=HERE/"near.json"
    if args.write:
        dest.write_text(json.dumps(result,indent=2)+"\n")
    else:
        assert result==json.loads(dest.read_text())
    print([(r["rate_cap"],r["root_hole"],r["best_other_uncredited"]) for r in result["censuses"]])


if __name__=="__main__":
    main()
