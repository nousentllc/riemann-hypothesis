"""Check the source pin, rebuild the critical original files, and kernel-check the research proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.'
ORIGINAL='40e56bab026552e089d7afcfeff08d2defb9c005'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
INHERITED=['FiniteCounts','AllDepth','FourLift','FourEven']
STUDY=['ProgressionGeometry','ProgressionGrowth','GrowthConsumer','OriginalGrowthConsumer',
       'RankOneConsumer','OriginalGrowthControl','ProgressionEndpoint','ExceptionalDilation',
       'CappedGrowth','FourSquareControl']
DIRECT=[PREFIX+'SummableOneDivAbsNormSq',PREFIX+'RankOneLocalDensityAlmostAll',
        PREFIX+'RankOneLocalDensitiesProductConverges','CompanionTheory.AutomorphicTheory.ThetaDilations.SwOne']
FLAGS=['-j1','--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
       '-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-DmaxHeartbeats=4000000']


def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()


def invoke(args,work,env=None):
    result=subprocess.run(args,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode or "declaration uses 'sorry'" in result.stdout or 'depends on axioms: [sorryAx' in result.stdout:
        raise RuntimeError(f'{args}\n{result.stdout}')
    return result.stdout.strip()


def replay(args,work):
    sdk=args.sdk.resolve()
    lib=args.mathlib.resolve()
    original=args.original.resolve()
    cache=args.objects.resolve()
    entries=json.loads((ROOT/'original_imports.json').read_text())
    manifest=json.loads((ROOT/'manifest.json').read_text())
    version=invoke([sdk/'bin/lean','--version'],work)
    if '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' not in version or invoke(['git','rev-parse','HEAD'],lib)!=MATHLIB:
        raise ValueError('Lean/Mathlib pin differs.')
    env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,
          [work,lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean'])))
    for name,row in entries.items():
        src=original/row['path']
        if blob(src.read_bytes())!=row['blob']:
            raise ValueError('Original source differs: '+name)
        rel=Path(*name.split('.')).with_suffix('.olean')
        if sha(cache/rel)!=row['used_olean_sha256']:
            raise ValueError('Dependency object differs: '+name)
        (work/rel).parent.mkdir(parents=True,exist_ok=True)
        (work/rel).symlink_to(cache/rel)
    print('Authenticated',len(entries),'source files and dependency objects.',flush=True)
    rebuilt=[]
    for mod in [*DIRECT[:-1],*INHERITED,*STUDY,DIRECT[-1],'EndpointAudit']:
        rel=Path(*mod.split('.')).with_suffix('.lean')
        if mod in DIRECT:
            src=original/rel
            if blob(src.read_bytes())!=manifest['anchors'][rel.name]['blob']:
                raise ValueError(mod)
        else:
            src=ROOT/('inherited' if mod in INHERITED else 'verification')/rel
        if mod in INHERITED and blob(src.read_bytes())!=manifest['inherited'][mod]:
            raise ValueError('Predecessor differs: '+mod)
        target=work/rel;target.parent.mkdir(parents=True,exist_ok=True)
        out=target.with_suffix('.olean')
        if out.is_symlink():out.unlink()
        shutil.copyfile(src,target)
        log=invoke([sdk/'bin/lean',*FLAGS,'-o',rel.with_suffix('.olean'),rel],work,env)
        klog=invoke([sdk/'bin/leanchecker','-v',mod],work,env)
        if 'replaying '+mod not in klog or 'sorryAx' in log:
            raise ValueError(mod+': '+log+' '+klog)
        rebuilt.append(dict(module=mod,source_sha256=sha(src),kernel=klog,
                   findings=[l for l in log.splitlines() if 'depends on axioms' in l or l.startswith('AUDIT ')]))
        print('Rebuilt and replayed',mod,flush=True)
    return dict(lean=version,mathlib=MATHLIB,original=ORIGINAL,original_dependency_count=len(entries),
                mit_object_matches=sum(x['used_olean_sha256']==x['official_olean_sha256'] for x in entries.values()),
                rebuilt=rebuilt)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['sdk','mathlib','original','objects']:p.add_argument('--'+arg,type=Path,required=True)
    p.add_argument('--write', action='store_true')
    args=p.parse_args()
    with tempfile.TemporaryDirectory() as d:
        result=replay(args,Path(d))
    path=ROOT/'verification/receipt.json'
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    elif json.loads(path.read_text())!=result:raise ValueError('Receipt differs')
    print('Receipt verified.')


if __name__=='__main__':
    main()
