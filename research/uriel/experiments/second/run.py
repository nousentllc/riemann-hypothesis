"""Execute the finite probes and their regression tests, preserving per-probe outputs."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

import mpmath
import analytic
import arithmetic
import geometry
import prime_windows
import finite_certificate

HERE = Path(__file__).resolve().parent


def dump(path,value):
    path.write_text(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,default=HERE/"results")
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True,exist_ok=True)
    outputs = {}
    for name,fn in (("analytic",analytic.run),("arithmetic",arithmetic.run),
                    ("cohomology",geometry.cohomology),("slopes",geometry.slopes),
                    ("prime_windows",prime_windows.run),("finite_certificate",finite_certificate.run)):
        path = out/(name+".json")
        dump(path,fn())
        outputs[path.name] = sha256(path.read_bytes()).hexdigest()
    proc = subprocess.run([sys.executable,"-B",str(HERE/"tests.py")],text=True,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,env={**os.environ,"URIEL_RESULTS":str(out)})
    (out/"tests.txt").write_text(proc.stdout)
    dump(out/"numerical_run.json",dict(outputs=outputs,python=platform.python_version(),
         mpmath=mpmath.__version__,platform=platform.system(),machine=platform.machine(),test_exit=proc.returncode))
    print(proc.stdout,end="")
    return proc.returncode


if __name__=="__main__":
    raise SystemExit(main())
