"""Compile and replay the original continuation/separation module in a reduced Laurent context."""
import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
SDK = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
HERE = Path(__file__).resolve().parent
BASE = 'Development.AbelianVarietyTheory.Proofs.DivisorProofs.'
LAURENT = BASE+'LaurentConstEqOfTendsto'
DEF = BASE+'SiegelWeilAnisotropic'
CONT = 'Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected'
DIR = 'Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.'
SEP = DIR+'IsExtAtOfDiff'
EXP = DIR+'ExpNeOfLt'


def file(name):
    return Path(*name.split('.')).with_suffix('.lean')


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    for k in ('repo','source','sdk','mathlib'):
        parser.add_argument('--'+k, type=Path, required=True)
    args = parser.parse_args()
    repo, source, sdk, mathlib = [getattr(args,k).resolve() for k in ('repo','source','sdk','mathlib')]
    receipt = dict(pin=PIN,sources={},modules={},scope='Reduced upstream context using the exact LaurentConst definition and uniqueness proof. The two original continuation modules are complete and compiled under their original names. No adelic inputs instantiated.')
    receipt['lean'] = subprocess.check_output([sdk/'bin/lean','--version'],text=True).strip()
    receipt['mathlib'] = subprocess.check_output(['git','-C',mathlib,'rev-parse','HEAD'],text=True).strip()
    if SDK not in receipt['lean'] or receipt['mathlib'] != MATHLIB:
        raise ValueError('Toolchain mismatch')

    def read(name, lines=None):
        rel=Path('src')/file(name)
        raw=(source/rel).read_bytes()
        expected=subprocess.check_output(['git','-C',repo,'rev-parse',PIN+':'+str(rel)],text=True).strip()
        if expected!=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(): raise ValueError(rel)
        part=b''.join(raw.splitlines(keepends=True)[lines[0]-1:lines[1]]) if lines else raw
        receipt['sources'][str(rel)] = dict(blob=expected,lines=lines or 'whole file',sha256=sha256(part).hexdigest())
        return part.decode()
    reduced = 'import Mathlib\nnoncomputable section\nopen Filter Topology\nnamespace GlobalTheory.ThetaInner\n'
    reduced += read(DEF,(13,14))+'\n'+read(LAURENT,(8,30))+'\nend GlobalTheory.ThetaInner\nend\n'
    checked = 'import '+SEP+'\nnamespace PositivityTheory.SiegelWeilFormula.AStep\n'
    checked += read(EXP,(13,20))+"""
theorem separation_control {m n : ℕ} (h : m < n) (B : ℂ)
    (s : (Complex.exp ((2*n-m : ℕ) : ℂ) - Complex.exp (m : ℂ)) * B = 0) : B = 0 :=
  (mul_eq_zero.mp s).resolve_left (sub_ne_zero.mpr (exp_ne_of_lt h))

theorem collision_control (n : ℕ) :
    (Complex.exp ((2*n-n : ℕ) : ℂ) - Complex.exp (n : ℂ)) * (1 : ℂ) = 0 := by
  rw [show 2*n-n=n by omega, sub_self, zero_mul]

#print axioms lawSep
#print axioms wrap
#print axioms exp_ne_of_lt
#print axioms separation_control
#print axioms collision_control
end PositivityTheory.SiegelWeilFormula.AStep
"""
    modules = [(LAURENT,reduced),(CONT,read(CONT)),(SEP,read(SEP)),('SeparationControl',checked)]
    with tempfile.TemporaryDirectory() as scratch:
        root=Path(scratch)
        libs=[root,mathlib/'.lake/build/lib/lean',*sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,libs)))
        for name,code in modules:
            path=file(name)
            (root/path).parent.mkdir(parents=True,exist_ok=True)
            (root/path).write_text(code)
            logs=[]
            for cmd in ([sdk/'bin/lean','-j1','--root=.','-o',path.with_suffix('.olean'),path],[sdk/'bin/leanchecker','-v',name]):
                r=subprocess.run(cmd,env=env,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
                print(name, r.returncode, r.stdout, flush=True)
                if r.returncode or 'sorryAx' in r.stdout or "uses 'sorry'" in r.stdout:raise SystemExit(r.returncode or 1)
                logs.append(r.stdout.strip())
            if 'replaying '+name not in logs[1]:raise ValueError(name)
            receipt['modules'][name]=dict(sha256=sha256(code.encode()).hexdigest(),logs=logs)
        if logs[0].count('depends on axioms:')!=5:raise ValueError('Missing reports')
    (HERE/'receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')


if __name__=='__main__':
    run()
