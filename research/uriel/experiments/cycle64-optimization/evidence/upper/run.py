"""Recompute the complete cap-12/5 upper-bound certificate at the saved adverse word."""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
# Selected by exploratory label search. The bound replay is deterministic at fixed inputs.
WORD = 2556884934454963932
THRESHOLD = Fraction(99,916)


def compile_program(name, folder):
    path = Path(folder)/name
    subprocess.run([os.environ.get("CXX","c++"), "-O3", "-std=c++17",
                    str(HERE/f"{name}.cpp"),"-o",str(path)],check=True)
    return path


def order_for_word(word, base=0, step=1):
    if step == 64:
        return [base]
    left = (word>>(step-1+base))&1
    return (order_for_word(word,base+left*step,2*step)
            + order_for_word(word,base+(1-left)*step,2*step))


def literal_vertex(word, support, q):
    """Recompute every directed difference on the witness without the C++ envelope."""
    sites = [t for t in range(64) if support>>t&1]
    denominators = {i:1 for i in sites}
    numerators = {i:0 for i in sites}
    rows = []
    for stride in (1,2,4,8,16,32):
        width = 64//stride
        for base in range(stride):
            active = [i for i in sites if i%stride == base]
            if not active:
                continue
            even = (word>>(stride-1+base))&1
            assert any((i//stride)%2 == even for i in active)
            odd = [i for i in active if (i//stride)%2 != even]
            holes = [h for h in range(1,width,2)
                     if all((i+stride*h)%64 not in active for i in active)]
            for i in odd:
                denominators[i] += width
                numerators[i] += 2*len(holes)
            if odd:
                rows.append((width,base,holes,odd))
    ranked = sorted(sites, key=lambda i:(q.denominator*numerators[i]-q.numerator*denominators[i],-i),
                    reverse=True)
    weights = {i:(12 if j<26 else 8 if j==26 else 0) for j,i in enumerate(ranked)}
    assert sum(weights.values()) == 320
    p = sum(weights[i]*numerators[i] for i in sites)
    k = sum(weights[i]*denominators[i] for i in sites)
    assert Fraction(p,k) == q
    return {"support":sites,"zero_rates_in_closure":[i for i in sites if not weights[i]],
            "partial_rate_leaf":ranked[26],"numerator_times_five":p,"denominator_times_five":k,
            "node_rows":[{"width":w,"base":c,"missing_local":hs,"odd_leaves":odds}
                         for w,c,hs,odds in rows]}


def generate():
    with TemporaryDirectory() as temp:
        oracle = compile_program("bound",temp)
        independent = compile_program("independent",temp)
        params = [str(WORD),str(THRESHOLD.numerator),str(THRESHOLD.denominator)]
        line = list(map(int,subprocess.check_output([oracle,*params],text=True).split()))
        repeat = list(map(int,subprocess.check_output([independent,*params],text=True).split()))
    word, a, c, max_excess, p, k, support, raw, unique, base_p, base_k, _ = line
    assert (word,a,c)==tuple(map(int,params)) and repeat[:3]==line[:3]
    assert [raw,unique] == repeat[3:5] and max_excess == max(repeat[5], repeat[6]) == 0
    assert c*base_p-a*base_k == repeat[6] and c*p-a*k == 0
    return {"label_word":str(WORD), "label_order":order_for_word(word),
            "rate_cap":"12/5","upper":str(THRESHOLD),"no_root_surplus":repeat[6],
            "root_hole_surplus":repeat[5],"root_hole_before_deduplication":raw,
            "root_hole_after_deduplication":unique,
            "half_supports_including_empty":3263443,"vertex":literal_vertex(word,support,THRESHOLD)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    output=generate()
    path=HERE/"results.json"
    if args.check:
        assert output==json.loads(path.read_text())
    else:
        path.write_text(json.dumps(output,indent=2)+"\n")
    print(output["upper"], output["root_hole_after_deduplication"],output["no_root_surplus"],
          output["root_hole_surplus"])


if __name__=="__main__":
    main()
