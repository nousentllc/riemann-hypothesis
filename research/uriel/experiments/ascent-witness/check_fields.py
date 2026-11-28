"""Certify the finite fields and class-group actions with PARI/GP 2.19.1."""
import argparse
from hashlib import sha256
import json
from math import prod
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent


def verify(program):
    source = HERE/"certify_fields.gp"
    p = subprocess.run([program,"-s","128000000","-q","-f",str(source)],
                       capture_output=True,text=True,timeout=180)
    if p.returncode or p.stderr.strip():
        raise ValueError(p.stderr or "GP exited with failure")
    lines = [json.loads(s) for s in p.stdout.splitlines() if s.strip()]
    if not lines or lines[0]!=["pari",[2,19,1]]:
        raise ValueError("Unexpected GP version or transcript")
    fields = {}
    for label,degree,disc,order,structure,certified,polynomial,fixed in lines[1:]:
        if label in fields or len(polynomial)!=degree+1 or certified != 1 or prod(structure)!=order:
            raise ValueError("Invalid certificate for " + label)
        fields[label] = {"degree":degree,"discriminant":disc,"class_number":order,
                         "class_group_cyclic_factors":structure,"bnfcertify_full":certified,
                         "defining_coefficients_high_to_low":polynomial,
                         "fixed_classes_for_the_two_order_three_automorphisms":fixed}
    if len(fields)!=7 or [fields["cyclotomic_"+str(n)]["class_number"] for n in (3,9,27)] != [1,1,1]:
        raise ValueError("Failed cyclotomic control")
    cubic = sorted(v["class_number"] for k,v in fields.items() if k.startswith("diagonal_cubic"))
    upper = [v for k,v in fields.items() if k.startswith("diagonal_over_zeta3")]
    if cubic!=[3,3] or sorted(v["class_number"] for v in upper)!=[9,36] or any(
            v["fixed_classes_for_the_two_order_three_automorphisms"]!=[9,9] for v in upper):
        raise ValueError("Failed two-prime control")
    return {"pari_version":"2.19.1","gp_script_sha256":sha256(source.read_bytes()).hexdigest(),
            "fields":fields}


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gp",required=True)
    print(json.dumps(verify(ap.parse_args().gp),indent=2,sort_keys=True))
