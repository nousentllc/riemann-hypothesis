"""Re-run the prescribed-gap experiments and compare their recorded evidence."""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ORIGINAL = '40e56bab026552e089d7afcfeff08d2defb9c005'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
NUMERIC = {
    'fields': [('field_controls.py', 'results.json')],
    'pairs': [('prime_rows.py', 'results.json')],
    'stitch': [('experiment.py', 'results.json'), ('transients.py', 'transients.json')],
    'slot': [('probe.py', 'results.json')],
    'scalar': [('extrema.py', 'results.json')],
    'roster': [('check.py', 'results.json')],
    'cross': [('run.py', 'results.json')],
}
UNITS = (*NUMERIC, 'join')
IMPORT = re.compile(r'^(?:public )?import\s+([\w.]+)', re.M)


def parsed(path):
    return json.loads(path.read_bytes())


def git(gitdir, *args):
    return subprocess.check_output(['git', '-C', gitdir, *args])


def require_equal(value, expected, description):
    if value != expected:
        raise ValueError(f'{description} differs from its record')


def invoke(script, cwd, *arguments):
    env = dict(os.environ)
    # Several scientific controls are expressed as Python assertions.
    env.pop('PYTHONOPTIMIZE', None)
    proc = subprocess.run([sys.executable, '-B', script, *[str(x) for x in arguments]],
                          cwd=cwd, env=env, text=True, capture_output=True)
    if proc.returncode:
        raise RuntimeError(f'{script.parent.name}/{script.name} failed\n{proc.stdout}\n{proc.stderr}')
    return json.loads(proc.stdout)


def compare_numeric(unit, build):
    rows = []
    for script, name in NUMERIC.get(unit, []):
        data = invoke(HERE / unit / script, build)
        require_equal(data, parsed(HERE / unit / name), f'{unit}/{name}')
        rows.append(f'{unit}/{name}')
    return rows


def slot_sources(source, repo):
    pins = parsed(HERE / 'slot/imports.json')
    prior = parsed(HERE / 'slot/prior_sources.json')
    groups = collections.defaultdict(dict)
    for module, row in pins.items():
        if module in prior:
            raw = prior[module].encode()
            path, commit = row['path'], row['commit']
        else:
            path, commit = 'src/' + module.replace('.', '/') + '.lean', ORIGINAL
            raw = (source / path).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require_equal(blob, row['blob'], path)
        groups[commit][path] = blob
    if repo:
        for rev, saved in groups.items():
            found = {}
            listing = git(repo, 'ls-tree', '-r', '-z', rev, '--', *saved)
            for entry in listing.rstrip(b'\0').split(b'\0'):
                info, path = entry.split(b'\t')
                found[path.decode()] = info.split()[2].decode()
            require_equal(found, saved, rev)
    return {'original_sources': len(pins) - len(prior), 'prior_sources': len(prior),
            'commits': sorted(groups), 'checked_git_trees': repo is not None}


def source_audit(unit, opts, build):
    if unit == 'roster':
        trace = parsed(HERE / unit / 'source.json')
        require_equal(trace['commit'], ORIGINAL, 'roster source revision')
        files = trace['source_paths_relative_to_src']
        for name, identity in files.items():
            path = 'src/' + name
            raw = (opts.source / path).read_bytes()
            require_equal(hashlib.sha256(raw).hexdigest(), identity['sha256'], path)
            oid = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            require_equal(oid, identity['git_blob'], path)
            if opts.git:
                require_equal(git(opts.git, 'rev-parse', ORIGINAL + ':' + path).decode().strip(), oid, path)
        return {'commit': ORIGINAL, 'original_files': len(files), 'checked_git_tree': opts.git is not None}
    if unit == 'slot':
        return slot_sources(opts.source, opts.git)
    if unit not in ('fields', 'pairs'):
        return None
    args = ['--source', opts.source]
    if opts.git:
        args.extend(['--git', opts.git])
    result = invoke(HERE / unit / 'audit.py', build, *args)
    expected = parsed(HERE / unit / 'audit.json')
    if unit == 'fields':
        expected['git_trees_checked'] = opts.git is not None
    require_equal(result, expected, unit + '/audit.json')
    return result


def make_view(modules, roots, dest, source, *, cold, opts):
    """Give single-root tools an authenticated merged library; optionally build absent objects."""
    dest.mkdir(parents=True, exist_ok=True)
    pins = parsed(HERE / 'fields/imports.json')
    known = set()
    def stage(module):
        if module in known or module not in pins:
            return
        row = pins[module]
        rel = Path(*module.split('.'))
        src = source / 'src' / rel.with_suffix('.lean')
        data = src.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require_equal(blob, row['git_blob'], str(rel))
        for dep in IMPORT.findall(data.decode()):
            stage(dep)
        target = dest / rel.with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        for root in roots:
            obj = root / rel.with_suffix('.olean')
            if obj.is_file() and hashlib.sha256(obj.read_bytes()).hexdigest() == row['cached_sha256']:
                target.symlink_to(obj)
                break
        else:
            if cold:
                sdk, math = opts.toolchain, opts.mathlib
                libs = [dest, math / '.lake/build/lib/lean',
                        *sorted((math / '.lake/packages').glob('*/.lake/build/lib/lean')), sdk / 'lib/lean']
                env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)), LEAN_SYSROOT=str(sdk))
                cmd = [sdk / 'bin/lean', '-j1', '--tstack=400000', '-DautoImplicit=false',
                       '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3', '-Dpp.unicode.fun=true',
                       '-DmaxHeartbeats=4000000', '--root=.', '-o', target, rel.with_suffix('.lean')]
                subprocess.run(cmd, cwd=source / 'src', env=env, check=True,
                               stdout=subprocess.DEVNULL)
        known.add(module)
    for name in modules:
        stage(name)


def semantics(unit, raw):
    # A cold build and a warm build prove the same declarations; the object encoding
    # and target triple can differ across hosts. Check all other receipt fields.
    data = dict(raw)
    for key in ('version', 'lean', 'provider'):
        if key in data:
            match = re.search(r'Lean \(version (\d+\.\d+\.\d+),.*commit ([0-9a-f]+)', data[key])
            if not match or match.group(1) != '4.33.1':
                raise ValueError(str(data[key]))
            data[key] = list(match.groups())
    if unit == 'fields':
        count = data.pop('fresh_originals') + data.pop('reused_originals')
        require_equal(count, data['pinned_original_modules'], 'field coverage')
    if unit == 'pairs':
        count = len(data.pop('freshly_compiled_originals')) + data.pop('reused_originals')
        require_equal(count, data['authenticated_original_sources'], 'prime-pair coverage')
        data.pop('supplement_olean_sha256')
    if unit in ('slot', 'join'):
        data.pop('rebuilt', None)
        data.pop('rebuilt_inputs', None)
        data.pop('fresh_originals', None)
        data.pop('reused_originals', None)
    return data


def replay(unit, opts, work):
    common = ['--toolchain', opts.toolchain, '--mathlib', opts.mathlib]
    if unit == 'stitch':
        args = common
    elif unit == 'pairs':
        view = work / 'pair-inputs'
        make_view(['Development.AutomorphicArithmetic.CharacterBoxes.PairGood'], opts.objects,
                  view, opts.source, cold=False, opts=opts)
        args = [*common, '--source', opts.source, '--work', work / 'pair-build', '--objects', view]
    elif unit == 'roster':
        view = work / 'roster-inputs'
        make_view(['Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar'],
                  opts.objects, view, opts.source, cold=True, opts=opts)
        args = [*common, '--source', opts.source / 'src', '--proof-lib', view]
    else:
        args = [*common, '--source', opts.source]
        for root in opts.objects:
            args.extend(['--objects', root])
    result = invoke(HERE / unit / 'replay.py', work, *args)
    require_equal(semantics(unit, result), semantics(unit, parsed(HERE / unit / 'kernel.json')),
                  unit + '/kernel.json')
    return f'{unit}/kernel.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=r"""Examples (run from the package root):
  python3 evidence/reproduce.py
  python3 evidence/reproduce.py --only fields --only pairs --audit --source /data/original --git /data/fork
  python3 evidence/reproduce.py --kernels --audit --source /data/original --git /data/fork \
      --toolchain /opt/lean-4.33.1 --mathlib /data/mathlib --objects /data/cache1 --objects /data/cache2

Numerical controls run by default. Source audits authenticate fields, pairs, slot and roster.
Lean runs require the pinned, already built Mathlib and Lean distribution. Original
project modules absent from the optional caches are compiled in private work areas.
A complete cold run can be expensive. Outputs are compared by parsed JSON equality;
the original records are never overwritten. stdout is a JSON verification summary.""")
    parser.add_argument('--only', choices=UNITS, action='append', help='select one unit; repeat to combine')
    parser.add_argument('--audit', action='store_true', help='verify source traces and dependency pins')
    parser.add_argument('--kernels', '--lean', action='store_true', help='elaborate and kernel-replay selected formal units')
    parser.add_argument('--skip-numeric', action='store_true', help='suppress the default numerical runs')
    for path in ('source', 'git', 'toolchain', 'mathlib'):
        parser.add_argument('--'+path, type=lambda s: Path(s).resolve())
    parser.add_argument('--objects', type=lambda s: Path(s).resolve(), action='append', default=[],
                        help='original object library directory; repeat for additional caches')
    args = parser.parse_args()
    chosen = list(dict.fromkeys(args.only or UNITS))
    need_source = (args.audit and any(u in ('fields','pairs','slot','roster') for u in chosen)) or (
        args.kernels and any(u not in ('stitch', 'scalar', 'cross') for u in chosen))
    if need_source and (not args.source or not (args.source / 'src').is_dir()):
        parser.error('--source must be a checkout with src/ for the selected checks')
    formal_requested = args.kernels and any(u not in ('scalar', 'cross') for u in chosen)
    if formal_requested and (not args.toolchain or not args.mathlib):
        parser.error('--kernels requires --toolchain and --mathlib')
    if formal_requested:
        revision = git(args.mathlib, 'rev-parse', 'HEAD').decode().strip()
        require_equal(revision, MATHLIB, 'Mathlib revision')
    for root in args.objects:
        if not root.is_dir():
            parser.error(f'object directory does not exist: {root}')
    report = {'numeric':[], 'audits':{}, 'kernels':[]}
    with tempfile.TemporaryDirectory(prefix='prescribed-gap-') as name:
        base = Path(name)
        for unit in chosen:
            work = base / unit
            work.mkdir()
            if not args.skip_numeric:
                report['numeric'].extend(compare_numeric(unit, work))
            if args.audit:
                audit = source_audit(unit, args, work)
                if audit is not None:
                    report['audits'][unit] = audit
            if args.kernels and unit not in ('scalar', 'cross'):
                report['kernels'].append(replay(unit, args, work))
    if not any(report.values()):
        parser.error('no checks apply to the selected unit and modes')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
