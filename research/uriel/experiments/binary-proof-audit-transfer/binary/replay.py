"""Authenticate original sources, build the selected complete modules, and kernel-replay targets."""
import argparse
import concurrent.futures
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
SDK = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
BASE = 'Development.AutomorphicSpectrum.Proofs.BlockDecomposition.'
TARGETS = {
    BASE+'LatticePointCountScaling': ['GlobalTheory.CompanionTheory.RiemannCore.main'],
    BASE+'LatticeCosetScaledRiemannSum': ['GlobalTheory.CompanionTheory.Equi.lat_sum'],
    BASE+'ArchimedeanBinaryGramDensity': ['GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test'],
    BASE+'FiniteProductDifferenceBound': ['GlobalTheory.CompanionTheory.Mass.MeanV.abs_prod_sub_prod_le_sum_powerset'],
    BASE+'EulerProductConvergenceBound': ['GlobalTheory.CompanionTheory.Mass.SumDev.sum_bounded_prod'],
}
OPTS = ['--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
      '-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-DmaxHeartbeats=4000000','-j1']


def output(cmd, **opts):
    result = subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,**opts)
    if result.returncode or 'declaration uses \'sorry\'' in result.stdout:
        raise RuntimeError(f'{cmd}:\n{result.stdout}')
    return result.stdout.strip()


def file(mod):
    return Path(*mod.split('.')).with_suffix('.lean')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ('source','repo','sdk','mathlib'):
        parser.add_argument('--'+key, type=Path,required=True)
    parser.add_argument('--untagged', action='store_true', help='Use default package metadata and relative filenames for the preliminary comparison.')
    parser.add_argument('--jobs',type=int,default=2)
    parser.add_argument('--build',type=Path,help='New empty build directory (default temporary)')
    parser.add_argument('--receipt',type=Path,default=HERE/'kernel_receipt.json')
    parser.add_argument('--reference',type=Path,help='Optional original published module SHA-256 manifest')
    args=parser.parse_args()
    src = args.source.resolve() / 'src'
    sdk = args.sdk.resolve()
    mathlib = args.mathlib.resolve()
    version=output([sdk/'bin/lean','--version'])
    rev=output(['git','-C',mathlib,'rev-parse','HEAD'])
    if SDK not in version or rev != MATHLIB:
        raise ValueError('Unexpected Lean/Mathlib toolchain')
    listing=subprocess.check_output(['git','-C',args.repo,'ls-tree','-rz',PIN,'--','src'])
    tree={}
    for record in listing.split(b'\0'):
        if record:
            head,path=record.split(b'\t',1)
            tree[Path(path.decode()).relative_to('src')]=head.split()[-1].decode()
    refs={}
    if args.reference:
        if sha256(args.reference.read_bytes()).hexdigest()!='375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25':
            raise ValueError('Unrecognized reference manifest')
        for line in args.reference.read_text().splitlines():
            digest,path=line.split(maxsplit=1)
            refs[Path(path)]=digest
    deps = {}
    inputs = {}
    def inspect_module(mod):
        if mod in deps:
            return
        path = file(mod)
        raw = (src / path).read_bytes()
        blob=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if tree.get(path) != blob:
            raise ValueError(f'Mismatch: {path}')
        inputs[mod]={'git_blob':blob,'source_sha256':sha256(raw).hexdigest()}
        names=re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+(\S+)',raw.decode(),re.MULTILINE)
        deps[mod]={name for name in names if file(name) in tree}
        for name in deps[mod]:
            inspect_module(name)
    for mod in TARGETS:
        inspect_module(mod)
    content=(src/file(BASE+'TestFunctionExists')).read_bytes()
    original=tree[file(BASE+'TestFunctionExists')]
    if sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()!=original:
        raise ValueError('Test-function source mismatch')
    selected=b''.join(content.splitlines(keepends=True)[15:48])
    reduced=("import Mathlib\nnoncomputable section\nopen MeasureTheory Topology Filter\n"
             "open scoped ENNReal NNReal Classical\nnamespace GlobalTheory.CompanionTheory.SW.MassTest\n").encode()+selected+b'\nend GlobalTheory.CompanionTheory.SW.MassTest\nend\n'
    checks={**TARGETS,'PositiveTestExtract':['GlobalTheory.CompanionTheory.SW.MassTest.exists_bump','GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen']}
    receipt={'pin':PIN,'lean':version,'mathlib':rev,'source_files':inputs,'original_modules':{},'replays':{},
             'positive_test_extract':{'source':str(Path('src')/file(BASE+'TestFunctionExists')),'blob':original,'lines':[16,48],
                                      'fragment_sha256':sha256(selected).hexdigest(),'module_sha256':sha256(reduced).hexdigest()},
             'scope':'Original modules, their exact project dependency closure, and a reduced-context test-function extract; prebuilt Mathlib. No full binary mass proof or RH endpoint replayed.'}
    with tempfile.TemporaryDirectory() as tmp:
        build=(args.build or Path(tmp)).resolve()
        if args.build:
            if build.exists() and any(build.iterdir()):
                raise ValueError('Build directory must be empty')
            build.mkdir(parents=True,exist_ok=True)
        for mod in deps:
            target=build/file(mod)
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes((src/file(mod)).read_bytes())
        (build/'PositiveTestExtract.lean').write_bytes(reduced)
        libs=[build,mathlib/'.lake/build/lib/lean',*sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,libs)))
        def compile_one(mod):
            relative = file(mod)
            obj = relative.with_suffix('.olean')
            if mod == 'PositiveTestExtract' or args.untagged:
                text=output([sdk/'bin/lean',*OPTS,'-o',str(obj),str(relative)],cwd=build,env=env)
            else:
                config=build/(mod+'.setup.json')
                config.write_text(json.dumps(dict(name=mod,package='tree',isModule=False,importArts={},plugins=[],dynlibs=[],options={})))
                source_label='/home/ubuntu/grh/src/lean/src/'+relative.as_posix()
                text=output([sdk/'bin/lean',*OPTS,'--root=.','--setup='+str(config),'-o',str(obj),'--stdin',source_label],
                            input=(build/relative).read_text(),cwd=build,env=env)
            actual=sha256((build/obj).read_bytes()).hexdigest()
            reference=refs.get(obj)
            return {'olean_sha256':actual,'reference_match':actual==reference if reference else None,'log':text}
        todo = dict(deps)
        todo['PositiveTestExtract'] = set()
        done = set()
        futures = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while todo or futures:
                for mod in sorted(tuple(todo)):
                    if todo[mod]<=done and len(futures)<args.jobs:
                        futures[pool.submit(compile_one, mod)] = mod
                        del todo[mod]
                if not futures:
                    raise RuntimeError('Unresolved import cycle')
                completed,_=concurrent.futures.wait(futures,return_when=concurrent.futures.FIRST_COMPLETED)
                for future in completed:
                    mod = futures.pop(future)
                    rec = future.result()
                    if mod == 'PositiveTestExtract':
                        receipt['positive_test_extract'].update(rec)
                    else:
                        receipt['original_modules'][mod] = rec
                    done.add(mod)
                    print(f'Built {len(done)}/{len(deps)+1} {mod}',flush=True)
        probes=''.join('import '+m+'\n' for m in checks)+'\n'
        probes+=''.join('#print axioms '+name+'\n' for names in checks.values() for name in names)
        (build/'Probe.lean').write_text(probes)
        probe=output([sdk/'bin/lean',*OPTS,'Probe.lean'],cwd=build,env=env)
        receipt['axioms']={n:[v.strip() for v in a.split(',')] for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",probe)}
        expected={n for names in checks.values() for n in names}
        if set(receipt['axioms'])!=expected or any(set(a)-{'propext','Classical.choice','Quot.sound'} for a in receipt['axioms'].values()):
            raise ValueError(probe)
        for mod in sorted(done):
            log=output([sdk/'bin/leanchecker','-v',mod],cwd=build,env=env)
            if 'replaying '+mod not in log:
                raise ValueError(log)
            receipt['replays'][mod]=log
            print(log,flush=True)
    args.receipt.write_text(json.dumps(receipt,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print(f'Confirmed {len(deps)} original modules, {len(done)} module replays, {len(expected)} audited declarations.')

if __name__ == '__main__':
    main()
