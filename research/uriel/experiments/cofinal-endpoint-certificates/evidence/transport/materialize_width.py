"""Materialize the unelaborated width-generic host wrapper from its authenticated original source."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError("source substitution did not match once: "+old)
    return text.replace(old,new,1)


def generate(source):
    manifest=json.loads((HERE/"source_map.json").read_text())
    hashes={entry["path"]:entry["sha256"] for entry in manifest["entries"]}
    def read(rel):
        data=(source/rel).read_bytes()
        if hashlib.sha256(data).hexdigest()!=hashes[rel]:
            raise ValueError(rel)
        return data.decode()
    base=read("src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean")
    data=replace_once(base, "theorem UpperTheory.T3.supplyOfAdmOf :", "theorem MarkedWindows.supplyOfAdmBelowTwo (lam : ℝ) (hlam : lam < 2) :")
    data=replace_once(data, "HostExW (3 / 2)", "HostExW lam")
    data=replace_once(data, "UpperTheory.Top.winPairs ψ eps (c : ℝ) heps heps' (by exact_mod_cast hc) hV QH.pairEx",
                      "MarkedWindows.winPairsBelowTwo ψ eps (c : ℝ) lam heps heps' (by exact_mod_cast hc) hlam hV QH.pairEx")
    original=read("src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean")
    prefix,wrapper=original.split("theorem UpperTheory.Top.supplyChi :",1)
    wrapper=replace_once(wrapper,"HostExW (3 / 2)","HostExW lam")
    wrapper=replace_once(wrapper,"refine supplyOfAdm ψ hψ ?_", "refine MarkedWindows.supplyOfAdmBelowTwo lam hlam UpperTheory.Top.hostOfField ψ hψ ?_")
    imports=[line for line in prefix.splitlines() if line.startswith("import ")]
    suffix="theorem MarkedWindows.supplyChiBelowTwo (lam : ℝ) (hlam : lam < 2) :"+wrapper
    # Repeating an open command between declaration bodies preserves the original namespaces.
    return "import MarkedWindows\n"+"\n".join(imports)+"\n"+data+"\n"+prefix[prefix.index("open "):]+suffix


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source",required=True,type=Path)
    ap.add_argument("--output",type=Path,help="write a fresh research file outside the original source tree")
    args=ap.parse_args()
    content=generate(args.source)
    if args.output:
        if args.output.resolve().is_relative_to(args.source.resolve()):
            ap.error("choose an output outside the original source")
        with args.output.open("x") as stream:
            stream.write(content)
    print(json.dumps({"generated_file":"WidthHost.lean","sha256":hashlib.sha256(content.encode()).hexdigest(),
                      "lines":len(content.splitlines()),"status":"Source-generation control executed; extended host wrapper not elaborated."},indent=2))
