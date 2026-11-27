"""Elaborate and kernel-replay the six new modules with the original imports."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
LAYERS = (
    ('Predecessor', 'NativeAccounting', 'TentWindow'),
    ('MatchedTau', 'InteractionBudget', 'WindowTransport'),
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(cmd, cwd=None, env=None):
    p = subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,
                       text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode or 'sorryAx' in p.stdout or 'declaration uses ' + chr(96) + 'sorry' in p.stdout:
        raise RuntimeError(f'{p.args!r}\n{p.stdout[-12000:]}')
    return p.stdout.strip()


def replay(name, work, sdk, env):
    f = HERE/(name+'.lean')
    shutil.copyfile(f,work/f.name)
    obj = work/(name+'.olean')
    elaborate = run([sdk/'bin/lean','-j1','-o',obj.name,f.name],work,env)
    kernel = run([sdk/'bin/leanchecker','-v',name],work,env)
    if f'replaying {name}' not in kernel:
        raise RuntimeError(f'Module replay missing from output for {name}')
    print(kernel,flush=True)
    return {'name':name,'source_sha256':sha(f),'object_sha256':sha(obj),
            'elaboration':elaborate,'kernel':kernel}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for k in ('source','sdk','mathlib','objects','receipt'):
        parser.add_argument('--'+k,type=Path,required=True)
    a = parser.parse_args()
    source,sdk,mathlib,objects = (getattr(a,k).resolve() for k in ('source','sdk','mathlib','objects'))
    version = run([sdk/'bin/lean','--version'])
    revision = run(['git','rev-parse','HEAD'],cwd=mathlib)
    if LEAN not in version or revision != MATHLIB:
        raise ValueError('Lean or Mathlib revision mismatch')
    trace = json.loads((HERE/'source_trace.json').read_text())
    for record in trace['files']:
        if sha(source/record['path']) != record['sha256']:
            raise ValueError(f"Original source hash mismatch: {record['path']}")
    deps = sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))
    if mathlib.parent.name=='packages':
        deps += sorted(mathlib.parent.glob('*/.lake/build/lib/lean'))
    with tempfile.TemporaryDirectory(prefix='frobenius-window-') as tmp:
        work = Path(tmp)
        env = dict(os.environ,LEAN_SYSROOT=str(sdk),
                   LEAN_PATH=os.pathsep.join(map(str,[work,objects,mathlib/'.lake/build/lib/lean',*deps])))
        modules = []
        with ThreadPoolExecutor(max_workers=2) as pool:
            for layer in LAYERS:
                modules.extend(pool.map(lambda name: replay(name,work,sdk,env),layer))
    receipt = {'original':trace['original'],'lean':version,'mathlib':revision,
               'verified_original_source_files':len(trace['files']),'modules':modules,
               'scope':'Prepared original objects. The source host supply, analytic strip weighting '
                       'and full asymptotic selection are written/source-traced, not rebuilt here.'}
    a.receipt.write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__':
    main()
