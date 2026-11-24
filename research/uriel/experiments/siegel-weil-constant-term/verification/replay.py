"""Rebuild and kernel-replay the pinned constant-term modules and source extracts."""
from __future__ import annotations

import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
LEAN = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
EXCH = 'Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Exch'
MODULES = {
    'Formalism.UnipotentAdelicQuotients.SWXSDefs': 'complete original',
    'ReciprocityTheory.Chebotarev.NZIdeal': 'complete original',
    'ReciprocityTheory.Chebotarev.EulerSum': 'complete original',
    EXCH: 'complete original',
    'OriginalSlices': 'original declarations in reduced import environment',
    'NormalFactors': 'original declarations in reduced import environment',
    'Controls': 'new local conclusions and boundary counterexample',
}

def run(args, **kwargs):
    proc = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kwargs)
    if proc.returncode:
        raise RuntimeError(proc.stdout.decode())
    return proc.stdout

def require(check, message):
    if not check:
        raise ValueError(message)

def blob(data):
    return sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def source_check(repo, extracted_tree):
    records = json.loads((HERE/'source_map.json').read_text())
    checked = 0
    for item in records.values():
        spec = PIN+':'+item['repository_path']
        if repo:
            tree_oid = run(['git','-C',repo,'rev-parse',spec]).decode().strip()
            require(tree_oid==item['blob'], 'Pinned Git path differs at '+item['repository_path'])
        if extracted_tree:
            raw = (extracted_tree/item['repository_path']).read_bytes()
        elif repo:
            raw = run(['git','-C',repo,'show',spec])
        else:
            raw = None
        if raw is not None:
            require(blob(raw)==item['blob'], 'Original bytes differ at '+item['repository_path'])
        for target, spans in item['targets'].items():
            data = (HERE/target).read_bytes()
            whole = target=='Exch.lean' or target.startswith('support/')
            if whole:
                require(blob(data)==item['blob'], 'Packaged whole module differs: '+target)
            destination = data.splitlines(keepends=True)
            for span in spans:
                a,b = span['target_lines']
                chunk = b''.join(destination[a-1:b])
                require(sha256(chunk).hexdigest()==span['sha256'], 'Edited source extract: '+target)
                if raw is not None:
                    p,q = span['original_lines']
                    require(chunk==b''.join(raw.splitlines(keepends=True)[p-1:q]), 'Git source differs: '+target)
                checked+=1
    return checked

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sdk',type=Path,required=True)
    parser.add_argument('--mathlib',type=Path,required=True)
    parser.add_argument('--git',type=Path,help='Compare every cited line to the actual original Git tree.')
    parser.add_argument('--source',type=Path,help='Extracted original tree containing src, for offline blob comparison.')
    parser.add_argument('--out',type=Path,help='Store the JSON receipt, default stdout.')
    args=parser.parse_args()
    sdk=args.sdk.resolve()
    math=args.mathlib.resolve()
    version=run([sdk/'bin/lean','--version']).decode().strip()
    require('4.33.1' in version and LEAN in version,'Lean binary pin mismatch')
    require(run(['git','-C',math,'rev-parse','HEAD']).decode().strip()==MATHLIB,'Mathlib pin mismatch')
    spans=source_check(args.git,args.source)
    report={'source_commit':PIN,'lean':version,'mathlib':MATHLIB,'source_spans_checked':spans,
            'compared_to_pinned_git_tree':bool(args.git),'module_replay':{},'axioms':{}}
    with tempfile.TemporaryDirectory(prefix='siegel-weil-replay-') as folder:
        root=Path(folder)
        libs=[root,math/'.lake/build/lib/lean',*sorted((math/'.lake/packages').glob('*/.lake/build/lib/lean')),sdk/'lib/lean']
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)),LEAN_SYSROOT=str(sdk),
                 PATH=str(sdk/'bin')+os.pathsep+os.environ['PATH'])
        for module,kind in MODULES.items():
            rel=Path(*module.split('.')).with_suffix('.lean')
            if module==EXCH:
                packaged=HERE/'Exch.lean'
            elif kind=='complete original':
                packaged=HERE/'support'/rel
            else:
                packaged=HERE/rel
            data=packaged.read_bytes()
            path=root/rel
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(data)
            log=run([sdk/'bin/lean','-j2','--root=.','-o',rel.with_suffix('.olean'),rel],cwd=root,env=env).decode()
            require('sorryAx' not in log and "declaration uses 'sorry'" not in log, 'Admitted proof in '+module)
            replay=run([sdk/'bin/leanchecker','-v',module],cwd=root,env=env).decode().strip()
            require('replaying '+module in replay,'Missing kernel replay for '+module)
            report['module_replay'][module]={'scope':kind,'sha256':sha256(data).hexdigest(),
                  'compiler_warnings':[s for s in log.splitlines() if 'warning:' in s],'leanchecker':replay}
        audit=(HERE/'Audit.lean').read_bytes()
        (root/'Audit.lean').write_bytes(audit)
        log=run([sdk/'bin/lean','-j2','--root=.','Audit.lean'],cwd=root,env=env).decode()
        for name in re.findall(r'^#print axioms (\S+)',audit.decode(),re.M):
            match=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
            if match:
                axioms=sorted(filter(None,(s.strip() for s in match[1].split(','))))
            else:
                require("'"+name+"' does not depend on any axioms" in log, 'Missing axiom audit for '+name)
                axioms=[]
            require(set(axioms)<={'propext','Classical.choice','Quot.sound'}, 'Unexpected axiom: '+name)
            report['axioms'][name]=axioms
    report['whole_constant_term_or_siegel_weil_replayed']=False
    out=json.dumps(report,indent=2,ensure_ascii=False)+'\n'
    if args.out:
        args.out.write_text(out)
    else:
        print(out,end='')

if __name__=='__main__':
    main()
