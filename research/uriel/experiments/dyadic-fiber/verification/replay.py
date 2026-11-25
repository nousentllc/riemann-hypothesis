"""Build the pinned import closure and replay the resulting theorem objects."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def invoke(args, cwd=None, env=None):
    process=subprocess.run(args,cwd=cwd,env=env,capture_output=True,text=True)
    output=(process.stdout+process.stderr).strip()
    if process.returncode:
        raise RuntimeError(f'{args}: {output}')
    return output

def replay(sdk, lib, build):
    manifest=json.loads((ROOT/'sources.json').read_text())
    lean=invoke([sdk/'bin/lean','--version'])
    revision=invoke(['git','-C',lib,'rev-parse','HEAD'])
    assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in lean
    assert revision=='0df444a360eaa60ab8c11dca51a86af692955474'
    env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(str(p) for p in
         [build,lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']))
    jobs=[(r['module'],ROOT/'source'/r['path'][4:]) for r in manifest['modules'] if r['compile']]
    jobs += [(p.stem,p) for p in sorted((ROOT/'verification').glob('*.lean'))]
    results=[]
    for module, source in jobs:
        target=Path(*module.split('.')).with_suffix('.lean')
        file=build/target
        file.parent.mkdir(parents=True,exist_ok=True)
        data=source.read_bytes()
        file.write_bytes(data)
        report=invoke([sdk/'bin/lean','-j1','-o',target.with_suffix('.olean'),target],cwd=build,env=env)
        kernel=invoke([sdk/'bin/leanchecker','-v',module],cwd=build,env=env)
        assert 'replaying '+module in kernel and "declaration uses 'sorry'" not in report and 'sorryAx' not in report
        results.append(dict(module=module,sha256=hashlib.sha256(data).hexdigest(),stdout=report,kernel=kernel))
        print(module,flush=True)
    return dict(lean=lean,mathlib=revision,modules=results)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--sdk',type=Path,required=True)
    p.add_argument('--mathlib',type=Path,required=True)
    p.add_argument('--write',action='store_true')
    a=p.parse_args()
    with tempfile.TemporaryDirectory() as d:
        result=replay(a.sdk.resolve(),a.mathlib.resolve(),Path(d))
    dest=ROOT/'verification/receipt.json'
    if a.write: dest.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(dest.read_text())==result

if __name__=='__main__': main()
