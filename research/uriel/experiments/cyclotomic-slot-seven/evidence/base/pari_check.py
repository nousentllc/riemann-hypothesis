"""Independent finite class-number comparisons. Requires PARI/GP; Python uses the standard library."""
import argparse
import json
import subprocess


def compute(gp, conductor, degree, timeout):
    polynomial = f"polsubcyclo({conductor},{degree})" if degree else f"polcyclo({conductor})"
    program = f"""
default(parisize,64000000);
default(parisizemax,384000000);
setrand(1);
P={polynomial};
B=bnfinit(P,1);
print([version(),poldegree(P),Vec(P),B.disc,B.no,B.cyc,bnfcertify(B)]);
quit;
"""
    result = subprocess.run([gp, "-fq"], input=program, capture_output=True, text=True, timeout=timeout)
    if result.returncode or any("***" in line and "Warning" not in line for line in result.stderr.splitlines()):
        raise RuntimeError(result.stderr)
    version, dimension, coefficients, disc, class_number, elementary, certified = json.loads(result.stdout.strip())
    if dimension != (degree or (conductor - conductor // 7)) or certified != 1:
        raise ValueError("Failed PARI class-group certification or wrong degree")
    return dict(conductor=conductor, degree=dimension, polynomial_descending=coefficients,
                discriminant=disc, class_number=class_number, cyclic_factors=elementary,
                bnfcertify=certified, pari_version=version)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--timeout",type=int,default=60)
    parser.add_argument("--attempt-full-49",action="store_true",help="also attempt the unbounded-cost test on the full degree-42 field")
    args=parser.parse_args()
    cases=[(7,0),(7,3),(49,7),(49,14)]
    if args.attempt_full_49:
        cases.append((49,0))
    print(json.dumps([compute(args.gp,*case,args.timeout) for case in cases],indent=2))


if __name__=="__main__":
    main()
