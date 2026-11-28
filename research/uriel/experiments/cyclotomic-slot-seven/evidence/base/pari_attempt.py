"""Optional bounded trials at conductor 49. A timeout leaves the initialization estimate conditional."""
import argparse
import json
import subprocess


def trial(gp,degree,flag,limit):
    polynomial="polcyclo(49)" if degree==42 else "polsubcyclo(49,21)"
    prog=f"""default(parisize,64000000);
default(parisizemax,384000000);
setrand(1);
P={polynomial};
B=bnfinit(P,1);
print(["estimate",B.disc,B.no,B.cyc]);
print(["certified",{flag},bnfcertify(B,{flag})]);
"""
    event="finished"
    try:
        proc=subprocess.run([gp,"-fq"],input=prog.encode(),capture_output=True,timeout=limit)
        if proc.returncode or any(b"***" in s and b"Warning" not in s for s in proc.stderr.splitlines()):
            raise RuntimeError(proc.stderr.decode())
        out=proc.stdout
    except subprocess.TimeoutExpired as e:
        out=e.stdout or b""
        event="timeout"
    return dict(degree=degree,certification_flag=flag,time_budget_seconds=limit,
                event=event,output=[json.loads(s) for s in out.splitlines()])


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--gp",default="gp")
    p.add_argument("--degree",type=int,choices=[21,42],required=True)
    p.add_argument("--flag",type=int,choices=[0,1],required=True)
    p.add_argument("--limit",type=int,required=True)
    a=p.parse_args()
    print(json.dumps(trial(a.gp,a.degree,a.flag,a.limit),indent=2))
