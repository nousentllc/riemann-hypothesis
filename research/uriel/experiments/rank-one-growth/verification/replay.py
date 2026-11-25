"""Compile from source and replay the saved Lean modules against the two pinned revisions."""
import argparse, hashlib, json, os, shutil, subprocess, tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
MODULES=['ReciprocityTheory.Chebotarev.NZIdeal','ReciprocityTheory.Chebotarev.EulerSum',
         'CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable','Inputs','Progression']
def run(args,**kw):
    p=subprocess.run(args,capture_output=True,text=True,**kw)
    out=(p.stdout+p.stderr).strip()
    if p.returncode: raise SystemExit(out)
    return out
def replay(sdk,lib):
    lean=run([sdk/'bin/lean','--version'])
    rev=run(['git','-C',lib,'rev-parse','HEAD'])
    assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in lean and rev=='0df444a360eaa60ab8c11dca51a86af692955474'
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,[root,lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean'])))
        results=[]
        for module in MODULES:
            f=Path(*module.split('.')).with_suffix('.lean');(root/f).parent.mkdir(parents=True,exist_ok=True)
            blob=(HERE/f).read_bytes();(root/f).write_bytes(blob)
            log=run([sdk/'bin/lean','-j1','-o',f.with_suffix('.olean'),f],cwd=root,env=env)
            check=run([sdk/'bin/leanchecker','-v',module],cwd=root,env=env)
            assert 'replaying '+module in check and 'sorry' not in log
            results.append(dict(module=module,sha256=hashlib.sha256(blob).hexdigest(),compiler=log,kernel=check))
            print(module,flush=True)
    return dict(lean=lean,mathlib=rev,modules=results)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--sdk',type=Path,required=True);p.add_argument('--mathlib',type=Path,required=True);p.add_argument('--write',action='store_true');a=p.parse_args()
    r=replay(a.sdk.resolve(),a.mathlib.resolve())
    path=HERE/'receipt.json'
    if a.write:path.write_text(json.dumps(r,indent=2)+'\n')
    else:assert r==json.loads(path.read_bytes())
