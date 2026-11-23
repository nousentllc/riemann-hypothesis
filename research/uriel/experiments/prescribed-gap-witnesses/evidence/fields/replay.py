"""Authenticate the original import closure, then elaborate and kernel-replay all supplements."""
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
import tempfile

HERE=Path(__file__).resolve().parent
PIN='40e56bab026552e089d7afcfeff08d2defb9c005'
MATH='0df444a360eaa60ab8c11dca51a86af692955474'
FLAGS=['-j1','--tstack=400000','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
       '-DmaxSynthPendingDepth=3','-Dpp.unicode.fun=true','-DmaxHeartbeats=4000000']
SUPPLEMENTS=['FieldEndpoints','CoherentFields','SynchronizedSlots','SuccessiveFields','PhysicalGap']

def relative(module,suffix):
    return Path(*module.split('.')).with_suffix(suffix)

def digest(file):
    return sha256(file.read_bytes()).hexdigest()

def get_graph(source,pins):
    graph={}
    def visit(name):
        if name in graph:
            return
        path=source/'src'/relative(name,'.lean')
        data=path.read_bytes()
        blob=sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if pins[name]['git_blob']!=blob:
            raise ValueError('Changed original source file: '+str(path))
        deps=re.findall(r'^(?:public )?import\s+([\w.]+)',data.decode(),re.M)
        graph[name]=[m for m in deps if (source/'src'/relative(m,'.lean')).exists()]
        for dep in graph[name]:
            visit(dep)
    for name in SUPPLEMENTS:
        for dep in re.findall(r'^(?:public )?import\s+([\w.]+)',(HERE/(name+'.lean')).read_text(),re.M):
            if (source/'src'/relative(dep,'.lean')).exists():
                visit(dep)
    if set(graph)!=set(pins):
        raise ValueError('Import closure differs from manifest')
    return graph

def replay(source,sdk,mathlib,objects,workers):
    pins=json.loads((HERE/'imports.json').read_bytes())
    graph=get_graph(source,pins)
    base=json.loads((HERE/'source_map.json').read_bytes())['prior']
    if digest(HERE/'FieldEndpoints.lean')!=base['sha256']:
        raise ValueError('Prior field interface changed')
    version=subprocess.check_output([sdk/'bin/lean','--version'],text=True).strip()
    math_pin=subprocess.check_output(['git','-C',mathlib,'rev-parse','HEAD'],text=True).strip()
    if not version.startswith('Lean (version 4.33.1,') or math_pin!=MATH:
        raise ValueError('Unexpected Lean/Mathlib version')
    with tempfile.TemporaryDirectory() as name:
        root=Path(name)
        libs=[root,mathlib/'.lake/build/lib/lean',*sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)),LEAN_SYSROOT=str(sdk),PATH=str(sdk/'bin')+os.pathsep+os.environ['PATH'])
        def run(cmd,cwd):
            p=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,capture_output=True,text=True)
            if p.returncode or "declaration uses 'sorry'" in p.stdout:
                raise RuntimeError(str(cmd[-1])+'\n'+p.stdout+p.stderr)
            return p.stdout.strip()
        def make(module):
            rel=relative(module,'.olean')
            dest=root/rel; dest.parent.mkdir(parents=True,exist_ok=True)
            for directory in objects:
                candidate=directory/rel
                if candidate.is_file() and digest(candidate)==pins[module]['cached_sha256']:
                    dest.symlink_to(candidate)
                    return False
            run([sdk/'bin/lean',*FLAGS,'--root=.','-o',dest,relative(module,'.lean')],source/'src')
            return True
        fresh=0
        pool=TopologicalSorter(graph);pool.prepare();ongoing={}
        with ThreadPoolExecutor(max_workers=workers) as th:
            while pool.is_active():
                for mod in pool.get_ready():
                    ongoing[th.submit(make,mod)]=mod
                done,_=wait(ongoing,return_when=FIRST_COMPLETED)
                for f in done:
                    fresh+=int(f.result())
                    pool.done(ongoing.pop(f))
        data={}
        for mod in SUPPLEMENTS:
            original=HERE/(mod+'.lean')
            staged=root/(mod+'.lean')
            shutil.copyfile(original,staged)
            published_hash=digest(staged)
            names=re.findall(r'^#print axioms ([\w.]+)$',original.read_text(),re.M)
            log=run([sdk/'bin/lean',*FLAGS,'--root=.','-o',mod+'.olean',mod+'.lean'],root)
            axes=[l for l in log.splitlines() if 'depends on axioms:' in l]
            if len(axes)!=len(names) or 'sorryAx' in log:
                raise ValueError('Unexpected axioms: '+log)
            if any(l.split("'")[1]!=n or not l.endswith('[propext, Classical.choice, Quot.sound]') for n,l in zip(names,axes)):
                raise ValueError('Axiom list mismatch: '+log)
            check=run([sdk/'bin/leanchecker','-v',mod],root)
            if check!='replaying '+mod:
                raise ValueError(check)
            data[mod]={'sha256':published_hash,'axioms':axes,'replay':check}
        return {'source_commit':PIN,'mathlib':MATH,'lean':version,'pinned_original_modules':len(pins),
                'fresh_originals':fresh,'reused_originals':len(pins)-fresh,'modules':data}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['source','toolchain','mathlib']:
        parser.add_argument('--'+key,type=Path,required=True)
    parser.add_argument('--objects',type=Path,action='append',default=[])
    parser.add_argument('--workers',type=int,default=3)
    opts=parser.parse_args()
    print(json.dumps(replay(opts.source.resolve(),opts.toolchain.resolve(),opts.mathlib.resolve(),
                            [p.resolve() for p in opts.objects],opts.workers),indent=2))
