"""Independently recompute the odd-character resultants in PARI/GP using inverse generators."""
import argparse
import json
from pathlib import Path
import subprocess

def run(gp, timeout):
    root = Path(__file__).resolve().parent
    primary = json.loads((root/"extended.json").read_bytes())
    # Derive the generator and coefficients in GP without calling the Python transform.
    script = """default(parisize,64000000);
default(parisizemax,384000000);
print(version());
calc(m)={my(d=eulerphi(m)/2,g=znprimroot(m)^(-1),P=sum(j=0,d-1,(m-2*lift(g^j))*x^j),z=polresultant(x^d+1,P));print([m,lift(g),z/(2*m)^(d-1)]);};
"""
    script += "\n".join("calc("+str(row["conductor"])+");" for row in primary["rows"])+"\nquit;\n"
    proc = subprocess.run([gp,"-fq"],input=script,text=True,capture_output=True,timeout=timeout,check=True)
    if any("***" in l and "Warning" not in l for l in proc.stderr.splitlines()):
        raise RuntimeError(proc.stderr)
    lines = proc.stdout.strip().splitlines()
    if len(lines) != 1+len(primary["rows"]):
        raise ValueError(proc.stdout)
    results = []
    for line, row in zip(lines[1:],primary["rows"]):
        m,g,h = json.loads(line)
        if m != row["conductor"] or str(h) != row["relative_class_number"]:
            raise ArithmeticError(m)
        results.append(dict(conductor=m,pari_generator=g,digits=len(str(h)),class_number_matches=True))
    return dict(pari=json.loads(lines[0]),method="polresultant using the inverse PARI primitive root",
                rows=results)

if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--gp",default="gp")
    p.add_argument("--timeout",type=int,default=120)
    a=p.parse_args()
    print(json.dumps(run(a.gp,a.timeout),indent=2))
