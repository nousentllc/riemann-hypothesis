"""Replay the new arithmetic-window bridge against the pinned analytic objects."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(toolchain, mathlib, objects):
    tc, ml, ob = (Path(p).resolve() for p in (toolchain, mathlib, objects))
    expected = json.loads((HERE / 'pinned_analytic_objects.json').read_text())
    for name, digest in expected['objects'].items():
        if sha(ob / (name.replace('.', '/') + '.olean')) != digest:
            raise ValueError('analytic object digest mismatch: ' + name)
    revision = subprocess.check_output(['git','-C',str(ml),'rev-parse','HEAD'], text=True).strip()
    if revision != '0df444a360eaa60ab8c11dca51a86af692955474':
        raise ValueError('Mathlib revision mismatch')
    with tempfile.TemporaryDirectory() as temp:
        cwd = Path(temp)
        mlpath = ml/'.lake/build/lib/lean'
        lib = [cwd, ob, mlpath, *sorted((ml/'.lake/packages').glob('*/.lake/build/lib/lean')), tc/'lib/lean']
        env = dict(os.environ, LEAN_SYSROOT=str(tc), LEAN_PATH=os.pathsep.join(map(str,lib)), PATH=str(tc/'bin')+os.pathsep+os.environ['PATH'])
        target = 'ArithmeticWindow'
        (cwd/(target+'.lean')).write_bytes((HERE/(target+'.lean')).read_bytes())
        def checked(cmd):
            p = subprocess.run([str(tc/'bin'/cmd[0]),*cmd[1:]],cwd=cwd,env=env,text=True,capture_output=True)
            if p.returncode:
                raise RuntimeError(p.stdout+'\n'+p.stderr)
            return (p.stdout+p.stderr).strip()
        version=checked(['lean','--version'])
        if 'version 4.33.1' not in version:
            raise ValueError('Lean version mismatch')
        declarations=checked(['lean','--root=.', '-o',target+'.olean',target+'.lean'])
        replay=checked(['leanchecker','-v',target])
        if 'replaying '+target != replay or 'sorryAx' in declarations:
            raise ValueError('Unexpected replay or unproved placeholder')
        return {'version':version,'mathlib_commit':revision,'analytic_objects_authenticated':len(expected['objects']),
                'source_sha256':sha(HERE/(target+'.lean')),'axioms':declarations,'kernel_output':replay,
                'scope':'New conditional bridge and two real-arithmetic equivalences. Given supply, all-index and local-core hypotheses, invokes original analytic theorem. No replay of upstream host construction.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    for p in ('toolchain','mathlib','objects'):ap.add_argument('--'+p,required=True,type=Path)
    a=ap.parse_args()
    print(json.dumps(run(a.toolchain,a.mathlib,a.objects),indent=2,ensure_ascii=False))
