"""Check pinned source files, compile the experiment and kernel-replay its modules."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from interface import source_excerpt

HERE = Path(__file__).resolve().parent
TOOLCHAINS = {
    'original': ('819816b2e0a3bf405af45ae5c7af2491d8f5bee6', '0df444a360eaa60ab8c11dca51a86af692955474'),
    'readable': ('eb6cafb7290e8bd5f2937522d8d804f58f02bafc', '56a005855ea17e0b0958f73ec801ae140b0a1679'),
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_inputs(edition, root):
    rows = json.loads((HERE / 'source_map.json').read_text())[edition]
    for row in rows['files']:
        if digest(root / row['path']) != row['sha256']:
            raise ValueError(f"Source mismatch in {edition}: {row['path']}")
    return rows['commit']

def run(source, module, work, sdk, libraries):
    experiment = work / (module + '.lean')
    shutil.copyfile(source, experiment)
    env = dict(os.environ, LEAN_SYSROOT=str(sdk),
               LEAN_PATH=os.pathsep.join(map(str, [work, *libraries, sdk / 'lib/lean'])))
    logs = {}
    for tool, args in [('lean', ['-j1', '-o', module + '.olean', experiment.name]),
                       ('leanchecker', ['-v', module])]:
        proc = subprocess.run([sdk / 'bin' / tool, *args], cwd=work, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (work / f'{module}.{tool}.log').write_text(proc.stdout)
        if proc.returncode or 'sorryAx' in proc.stdout or 'declaration uses ' + chr(96) + 'sorry' in proc.stdout:
            raise RuntimeError(f'{tool} failed on {module}\n{proc.stdout[-4000:]}')
        logs[tool] = proc.stdout.strip()
    print('replayed', module, flush=True)
    return dict(module=module, source_sha256=digest(source),
                object_sha256=digest(experiment.with_suffix('.olean')),
                elaboration=logs['lean'], kernel=logs['leanchecker'])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['readable', 'original', 'joint'])
    parser.add_argument('--sdk', type=Path, required=True)
    for option in ['original', 'readable', 'old-objects', 'old-mathlib', 'work', 'receipt']:
        parser.add_argument('--' + option, type=Path)
    args = parser.parse_args()
    sdk = args.sdk.resolve()
    pins = {}
    for edition in ['original', 'readable']:
        if args.mode in [edition, 'joint']:
            root = getattr(args, edition)
            if not root:
                parser.error(f'Supply --{edition} for {args.mode} mode.')
            pins[edition] = verify_inputs(edition, root)
    if args.mode == 'original':
        if not args.old_objects or not args.old_mathlib:
            parser.error('Supply --old-objects and --old-mathlib for the original pin.')
        mathlib = args.old_mathlib.resolve()
        libraries = [args.old_objects.resolve(), mathlib / '.lake/build/lib/lean',
                     *sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))]
        modules = ['OriginalWitness']
        toolchain = 'original'
    else:
        new = args.readable.resolve()
        mathlib = new / '.lake/packages/mathlib'
        libraries = [new / '.lake/build/lib/lean',
                     *sorted((new / '.lake/packages').glob('*/.lake/build/lib/lean'))]
        modules = ['ReadableDatum', 'ScaleControl']
        toolchain = 'readable'
        if args.mode == 'joint':
            if source_excerpt(args.original.resolve()).encode() != (HERE / 'WitnessInterface.lean').read_bytes():
                raise ValueError('Old declaration excerpt does not match pinned sources.')
            modules = ['WitnessInterface', 'ReadableDatum', 'ScaleControl', 'HostComparison']
    version = subprocess.check_output([sdk / 'bin/lean', '--version'], text=True).strip()
    mathlib_sha = subprocess.check_output(['git', '-C', mathlib, 'rev-parse', 'HEAD'], text=True).strip()
    lean_pin, mathlib_pin = TOOLCHAINS[toolchain]
    if lean_pin not in version or mathlib_sha != mathlib_pin:
        raise ValueError('Unexpected Lean or Mathlib revision.')
    with tempfile.TemporaryDirectory() as tmp:
        work = (args.work or Path(tmp)).resolve()
        work.mkdir(parents=True, exist_ok=True)
        rows = [run(HERE / (mod + '.lean'), mod, work, sdk, libraries) for mod in modules]
    if args.receipt:
        args.receipt.write_text(json.dumps(dict(mode=args.mode, source_pins=pins,
            compiler=version, mathlib=mathlib_sha, modules=rows), indent=2) + '\n')

if __name__ == '__main__':
    main()
