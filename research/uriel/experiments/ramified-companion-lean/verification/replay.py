"""Rebuild the study graph and run the standard kernel checker on each object."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory
from negative_control import check as check_negative
from dilate_negative import check as check_dilate_negative
from companion_negative import check as check_companion_negative

ROOT=Path(__file__).resolve().parents[1]
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
COMPILER='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def run(sdk,lib,objects,work,workers,original):
    inventory=json.loads((ROOT/'study_imports.json').read_text())
    originals=json.loads((ROOT/'original_imports.json').read_text())
    for m,row in originals.items():
        file=objects/Path(*m.split('.')).with_suffix('.olean')
        if digest(file)!=row['used_olean_sha256']:raise ValueError('Object differs '+m)
        if original:
            b=(original/row['path']).read_bytes()
            if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=row['blob']:
                raise ValueError('Pinned source differs '+m)
    version=subprocess.check_output([sdk/'bin/lean','--version'],text=True).strip()
    if COMPILER not in version:raise ValueError(version)
    if subprocess.check_output(['git','-C',lib,'rev-parse','HEAD'],text=True).strip()!=PIN:raise ValueError('Mathlib checkout')
    work.mkdir(parents=True,exist_ok=True)
    mods=inventory['modules']
    dep={m:set(row['imports'])&mods.keys() for m,row in mods.items()}
    env=dict(os.environ,LEAN_SYSROOT=str(sdk),LEAN_PATH=os.pathsep.join(map(str,[work,objects,
        lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean'])))
    done={};running={};waiting=set(mods)
    def check(m,inputs):
        source=ROOT/mods[m]['file']; record=work/(m+'.record.json')
        sig=hashlib.sha256((version+digest(source)+json.dumps(inputs,sort_keys=True)+digest(ROOT/'original_imports.json')).encode()).hexdigest()
        obj=work/(m+'.olean')
        if record.exists() and obj.exists():
            cached=json.loads(record.read_text())
            if cached['input_key']==sig and cached['object']==digest(obj):return cached
        (work/(m+'.lean')).write_bytes(source.read_bytes())
        logs=[]
        for cmd in [[sdk/'bin/lean','-j1','-o',m+'.olean',m+'.lean'],[sdk/'bin/leanchecker','-v',m]]:
            res=subprocess.run(cmd,cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            logs.append(res.stdout)
            if res.returncode:raise RuntimeError(m+'\n'+res.stdout[-3500:])
        match=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",logs[0])
        axioms={k:sorted(s.strip() for s in v.split(',') if s.strip()) for k,v in match}
        for k,vs in axioms.items():
            if set(vs)-{'propext','Classical.choice','Quot.sound'}:raise ValueError((m,k,vs))
        output=dict(source=digest(source),object=digest(obj),input_key=sig,axiom_queries=axioms,
                    lean_exit=0,leanchecker_exit=0)
        if m=='UncappedAudit':
            audit=next(line for line in logs[0].splitlines() if line.startswith('All-multiples closure:'))
            if audit!=(ROOT/'verification/dependencies.txt').read_text().strip():raise ValueError(audit)
            output['dependency_audit']=audit
        if m=='RamDependencyAudit':
            audit=next(line for line in logs[0].splitlines() if line.startswith('Named-place audit:'))
            if audit!=(ROOT/'verification/ramified_dependencies.txt').read_text().strip():raise ValueError(audit)
            output['dependency_audit']=audit
        if m=='DilateAudit':
            audit=next(line for line in logs[0].splitlines() if line.startswith('Square-dilate audit:'))
            if audit!=(ROOT/'verification/dilate_dependencies.txt').read_text().strip():raise ValueError(audit)
            output['dependency_audit']=audit
        record.write_text(json.dumps(output,sort_keys=True));return output
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        while waiting or running:
            for m in sorted(waiting):
                if len(running)>=workers:break
                if dep[m]<=done.keys():
                    running[ex.submit(check,m,{d:done[d]['input_key'] for d in dep[m]})]=m
                    waiting.remove(m)
            if not running:raise ValueError('Cyclic graph')
            finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in finished:
                m=running.pop(f);done[m]=f.result()
                print(f'{len(done):02d}/{len(mods)} {m}',flush=True)
    return dict(compiler=version,mathlib=PIN,negative_control=check_negative(sdk/'bin/lean',env,work),original_objects=len(originals),verified_source_blobs=len(originals) if original else 0,
        dilate_negative_control=check_dilate_negative(sdk/'bin/lean',env,work),
        companion_wrong_sign=check_companion_negative(sdk/'bin/lean',env,work),
        modules={m:{k:v for k,v in rec.items() if k not in ('input_key','object')} for m,rec in sorted(done.items())})
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('sdk','mathlib','objects'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--original',type=Path);p.add_argument('--work',type=Path)
    p.add_argument('--jobs',type=int,choices=(1,2,3,4),default=2)
    p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    with TemporaryDirectory() as tmp:
        r=run(a.sdk.resolve(),a.mathlib.resolve(),a.objects.resolve(),(a.work or Path(tmp)).resolve(),a.jobs,a.original)
    out=json.dumps(r,sort_keys=True,indent=1)+'\n'
    if a.receipt:a.receipt.write_text(out)
    else:print(out)
