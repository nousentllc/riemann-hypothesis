"""Compile the pinned local closure and replay its declarations with the Lean kernel."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def invoke(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return (result.stdout + result.stderr).strip()


def replay(sdk, lib, work, receipt, compiled):
    manifest = json.loads((ROOT / 'manifest.json').read_text())
    version = invoke([sdk / 'bin/lean', '--version'], ROOT)
    revision = invoke(['git', 'rev-parse', 'HEAD'], lib)
    if manifest['lean'] not in version or revision != manifest['mathlib']:
        raise ValueError('Toolchain or mathlib revision differs from the study pin.')
    libraries = [work, lib / '.lake/build/lib/lean',
                 *sorted((lib / '.lake/packages').glob('*/.lake/build/lib/lean')), sdk / 'lib/lean']
    env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str,libraries)))
    results = []
    for row in manifest['modules']:
        name = row['module']
        rel = Path(*name.split('.')).with_suffix('.lean')
        source = ROOT / row['path']
        data = source.read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError(f'Source drift in {name}')
        target = work / rel
        target.parent.mkdir(parents=True,exist_ok=True)
        flags = ['-j1','--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
                 '-DmaxSynthPendingDepth=3','-DmaxHeartbeats=4000000'] if row['kind']=='pinned' else ['-j2']
        if compiled:
            if target.read_bytes()!=data or not target.with_suffix('.olean').exists():
                raise ValueError(f'Working build incomplete at {name}')
        else:
            shutil.copyfile(source,target)
            log = invoke([sdk/'bin/lean',*flags,'-o',rel.with_suffix('.olean'),rel],work,env)
            if 'sorryAx' in log or "declaration uses 'sorry'" in log:
                raise ValueError(f'Placeholder in {name}')
        log = invoke([sdk/'bin/leanchecker','-v',name], work, env)
        if 'replaying '+name not in log:
            raise ValueError(f'Missing kernel replay for {name}')
        results.append(dict(module=name,source_sha256=row['sha256'],kernel=log))
        print(name,flush=True)
    audit = ['TargetOne.count_all','TargetOne.count_late','TargetOne.trace_coords',
             'TargetOne.tube_three_quarters','TargetOne.target_one_mass','TargetOne.realized_unconditionally']
    driver = work / 'AuditAxioms.lean'
    driver.write_text('import Existence\n'+''.join('#print axioms '+n+'\n' for n in audit))
    log = invoke([sdk/'bin/lean',driver.name],work,env)
    for name in audit:
        if f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in log:
            raise ValueError('Unexpected axioms: '+log)
    record=dict(toolchain=version,mathlib=revision,kernel_replay=results,axiom_report=log)
    if receipt:
        receipt.write_text(json.dumps(record,indent=2)+'\n')
    elif record!=json.loads((ROOT/'verification/receipt.json').read_text()):
        raise ValueError('Replay differs from the published receipt.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk',required=True,type=Path)
    parser.add_argument('--mathlib',required=True,type=Path)
    parser.add_argument('--existing-build',type=Path,help='Audit objects already compiled in this directory.')
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        work=args.existing_build.resolve() if args.existing_build else Path(temp)
        replay(args.sdk.resolve(),args.mathlib.resolve(),work,args.receipt,bool(args.existing_build))


if __name__=='__main__':
    main()
