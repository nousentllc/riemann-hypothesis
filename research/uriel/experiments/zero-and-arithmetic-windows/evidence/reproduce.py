"""Run the finite checks. Optional original-source and pinned Lean replay."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
HERE=Path(__file__).resolve().parent
def compare(a,b):
    # Floating diagnostics use host libm; exact integers, strings and rational
    # enclosure endpoints must match verbatim. Tiny diagnostic zeros can vary.
    if isinstance(a,float) and isinstance(b,(float,int)):
        return math.isclose(a,b,rel_tol=2e-10,abs_tol=2e-13)
    if isinstance(a,dict) and isinstance(b,dict):
        return a.keys()==b.keys() and all(compare(a[k],b[k]) for k in a)
    if isinstance(a,list) and isinstance(b,list):
        return len(a)==len(b) and all(compare(i,j) for i,j in zip(a,b))
    return a==b
def run(tool,archive,args=(),skip=(),floating=False):
    script=HERE/tool
    proc=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=script.parent,capture_output=True,text=True)
    if proc.returncode:raise RuntimeError(proc.stderr+'\n'+proc.stdout)
    saved=json.loads((HERE/archive).read_text());current=json.loads(proc.stdout)
    for k in skip:
        saved.pop(k,None);current.pop(k,None)
    if not (compare(current,saved) if floating else current==saved):raise ValueError(f'Output differs: {archive}')
    print('PASS',tool,flush=True)
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ('source','objects','mathlib','toolchain'):parser.add_argument('--'+key,type=Path)
    a=parser.parse_args()
    args={k:v.resolve() for k,v in vars(a).items() if v}
    if set(args)-{'source'} and len(args)!=4:parser.error('Supply all four Lean/source options for kernel replay.')
    for line in (HERE/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        if hashlib.sha256((HERE/name).read_bytes()).hexdigest()!=digest:raise ValueError(f'Integrity mismatch: {name}')
    print('PASS stored source and result digests',flush=True)
    run('models/probe.py','models/results.json',floating=True)
    run('models/delay.py','models/delay.json',floating=True)
    run('primes/prime_mass.py','primes/results.json')
    run('primes/chi4_closed.py','primes/chi4_closed.json')
    check=['--source',args['source']] if args else []
    run('arith/check_arithmetic.py','arith/control_receipt.json',check,() if args else ('authenticated_source_files',))
    run('arith/width_followup.py','arith/width_result.json')
    if len(args)==4:
        opts=sum((['--'+k,v] for k,v in args.items()),[])
        run('analytic/replay_window_mass.py','analytic/window_mass_replay.json',opts,('object_sha256_this_build','lean'))
        run('arith/replay.py','arith/kernel_receipt.json',sum((['--'+k,v] for k,v in args.items() if k!='source'),[]),('version',))
if __name__=='__main__':main()

