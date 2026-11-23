"""Authenticate source and previously sealed imports, build missing originals, replay successive prime-pair certificate."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from graphlib import TopologicalSorter
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PIN='40e56bab026552e089d7afcfeff08d2defb9c005'
MATH='0df444a360eaa60ab8c11dca51a86af692955474'
TARGETS=['Development.AutomorphicArithmetic.CharacterBoxes.PairGood']
FLAGS=['-j1','--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-DmaxHeartbeats=4000000']
def part(name,suffix):
    return Path(*name.split('.')).with_suffix(suffix)
def hash_file(file):
    return sha256(file.read_bytes()).hexdigest()
def closure(source):
    graph={}
    def visit(name):
        if name in graph:return
        p=source/'src'/part(name,'.lean')
        deps=[m for m in re.findall(r'^(?:public )?import\s+([\w.]+)',p.read_text(),re.M) if (source/'src'/part(m,'.lean')).is_file()]
        graph[name]=deps
        for m in deps:visit(m)
    for t in TARGETS:visit(t)
    return graph
def pin_source(args,graph):
    manifest=json.loads((HERE/'imports.json').read_bytes())['modules']
    for name in graph:
        rel=part(name,'.lean')
        raw=(args.source/'src'/rel).read_bytes()
        blob=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if blob != manifest[name]['git_blob']:raise ValueError('source hash '+name)
    return manifest
def main():
    cli=argparse.ArgumentParser(description=__doc__)
    for k in ('source','mathlib','toolchain','work'):
        cli.add_argument('--'+k,required=True,type=Path)
    cli.add_argument('--objects',type=Path)
    cli.add_argument('--workers',type=int,default=3)
    cli.add_argument('--originals-only',action='store_true')
    a=cli.parse_args()
    for k in ('source','mathlib','toolchain','work','objects'):
        if getattr(a,k): setattr(a,k,getattr(a,k).resolve())
    graph=closure(a.source)
    manifest=pin_source(a,graph)
    sdk,lib=a.toolchain,a.mathlib
    version=subprocess.check_output([sdk/'bin/lean','--version'],text=True).strip()
    mathpin=subprocess.check_output(['git','-C',lib,'rev-parse','HEAD'],text=True).strip()
    if not version.startswith('Lean (version 4.33.1,') or mathpin!=MATH:raise ValueError('pinned toolchain required')
    obj=a.work/'lib'; obj.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_SYSROOT=str(sdk),PATH=str(sdk/'bin')+os.pathsep+os.environ['PATH'])
    env['LEAN_PATH']=os.pathsep.join(map(str,[obj,lib/'.lake/build/lib/lean',*sorted((lib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']))
    def run(cmd,cwd):
        r=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,capture_output=True,text=True)
        if r.returncode or "declaration uses 'sorry'" in r.stdout:raise RuntimeError(str(cmd[-1])+'\n'+r.stdout+r.stderr)
        return r.stdout.strip()
    seal=a.work/'original_receipt.json'
    built=json.loads(seal.read_bytes()) if seal.is_file() else {}
    def get(name):
        rel=part(name,'.olean');dest=obj/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        if name in built and dest.is_file() and hash_file(dest)==built[name]['sha256']:return built[name]
        old=a.objects/rel if a.objects else None
        if old and old.is_file() and manifest[name].get('reference_olean')==hash_file(old):
            if dest.exists() and hash_file(dest)!=manifest[name]['reference_olean']:
                raise ValueError('unexpected existing object '+name)
            if not dest.exists():dest.symlink_to(old)
            return {'source':'authenticated prior object','sha256':hash_file(dest)}
        run([sdk/'bin/lean',*FLAGS,'--root=.','-o',dest,part(name,'.lean')],a.source/'src')
        return {'source':'freshly compiled','sha256':hash_file(dest)}
    scheduler=TopologicalSorter(graph);scheduler.prepare();futures={}
    with ThreadPoolExecutor(max_workers=a.workers) as ex:
        while scheduler.is_active():
            for n in scheduler.get_ready():futures[ex.submit(get,n)]=n
            done,_=wait(futures,return_when=FIRST_COMPLETED)
            for f in done:
                n=futures.pop(f);built[n]=f.result();scheduler.done(n)
            seal.write_text(json.dumps(built,sort_keys=True))
    if a.originals_only:
        print(json.dumps({'original_sources':len(graph),'freshly_compiled':sum(x['source']=='freshly compiled' for x in built.values())}))
        return
    supp=HERE/'PairSharing.lean'
    location=a.work/'supplement';location.mkdir(exist_ok=True)
    shutil.copyfile(supp,location/supp.name)
    names=re.findall(r'^#print axioms ([\w.]+)$',supp.read_text(),re.M)
    log=run([sdk/'bin/lean',*FLAGS,'--root=.','-o',obj/'PairSharing.olean','PairSharing.lean'],location)
    axes=[l for l in log.splitlines() if 'depends on axioms:' in l]
    if axes != [f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names] or 'sorryAx' in log:raise ValueError(log)
    if any(l.split("'")[1]!=n for n,l in zip(names,axes)):raise ValueError(log)
    check=run([sdk/'bin/leanchecker','-v','PairSharing'],location)
    if check!='replaying PairSharing':raise ValueError(check)
    print(json.dumps(dict(source_commit=PIN,authenticated_original_sources=len(graph),mathlib=mathpin,lean=version,
        supplement_sha256=hash_file(location/supp.name),supplement_olean_sha256=hash_file(obj/'PairSharing.olean'),freshly_compiled_originals=sorted(n for n,rec in built.items() if rec['source']=='freshly compiled'),
        reused_originals=sum(rec['source']=='authenticated prior object' for rec in built.values()),
        declarations=names,axioms=axes,kernel=check),indent=2))
if __name__=='__main__':main()
