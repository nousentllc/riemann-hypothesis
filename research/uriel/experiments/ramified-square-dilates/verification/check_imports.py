"""Replay all selected project declarations over the pinned compiled Mathlib base."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

ROOT=Path(__file__).resolve().parents[1]


def run(sdk,lib,objects,record):
    data=json.loads((ROOT/'original_imports.json').read_text())
    for name,row in data.items():
        artifact=objects/Path(*name.split('.')).with_suffix('.olean')
        if hashlib.sha256(artifact.read_bytes()).hexdigest()!=row['used_olean_sha256']:
            raise ValueError('Dependency object differs: '+name)
    if subprocess.check_output(['git','-C',lib,'rev-parse','HEAD'],text=True).strip()!='0df444a360eaa60ab8c11dca51a86af692955474':
        raise ValueError('Mathlib pin differs')
    if '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' not in subprocess.check_output([sdk/'bin/lean','--version'],text=True):
        raise ValueError('Lean pin differs')
    with TemporaryDirectory() as tmp:
        names=Path(tmp)/'imports.txt'
        names.write_text('\n'.join(sorted(data))+'\n')
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,[
            objects,lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean'])))
        result=subprocess.check_output([sdk/'bin/lean','-j1','--tstack=400000','--run',
            ROOT/'verification/ReplayImports.lean',names],cwd=tmp,env=env,text=True).strip()
    if record:record.write_text(result+'\n')
    expected=(record or ROOT/'verification/import_replay.txt').read_text().strip()
    if result!=expected:raise ValueError(result)
    print(result)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ('sdk','mathlib','objects'):p.add_argument('--'+arg,type=Path,required=True)
    p.add_argument('--record',type=Path)
    args=p.parse_args()
    run(args.sdk.resolve(),args.mathlib.resolve(),args.objects.resolve(),args.record)
