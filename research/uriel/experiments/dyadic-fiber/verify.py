"""Verify the source bytes, graph anchors, original/new distinction and saved replay."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from subprocess import check_output

ROOT=Path(__file__).resolve().parent

def read(name):
    return json.loads((ROOT/name).read_bytes())

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(repo=None, mathlib=None, graph=None):
    manifest=read('sources.json')
    checked={}
    for entry in manifest['modules']:
        path=ROOT/'source'/entry['path'][4:]
        data=path.read_bytes()
        oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert oid==entry['blob'] and digest(data)==entry['sha256']
        if repo:
            git_oid=check_output(['git','-C',repo,'rev-parse',manifest['pin']+':'+entry['path']]).decode().strip()
            assert oid==git_oid
        if entry['compile']: checked[entry['module']]=digest(data)
    supplemental=read('mathlib.json')
    if mathlib:
        for ref in supplemental['files']:
            data=check_output(['git','-C',mathlib,'show',supplemental['revision']+':'+ref['path']])
            assert digest(data)==ref['sha256']
    anchors=read('anchors.json')
    wanted={r['id']:r for r in anchors['anchors']}
    for a in wanted.values():
        line=(ROOT/'source'/a['file']).read_text().splitlines()[a['line']-1]
        assert a['name'].split('.')[-1] in line
    if graph:
        with graph.open('rb') as f: assert hashlib.file_digest(f,'sha256').hexdigest()==anchors['graph_sha256']
        seen=set()
        with gzip.open(graph,'rb') as f:
            for line in f:
                if not line.startswith(b'{"id":'):continue
                d=json.loads(line.rstrip().rstrip(b','))
                if d['id'] in wanted:
                    assert all(d[k]==v for k,v in wanted[d['id']].items())
                    seen.add(d['id'])
                    if seen==wanted.keys():break
        assert seen==wanted.keys()
    for path in (ROOT/'verification').glob('*.lean'):
        checked[path.stem]=digest(path.read_bytes())
    receipt=read('verification/receipt.json')
    assert receipt['mathlib']==supplemental['revision']
    assert checked=={r['module']:r['sha256'] for r in receipt['modules']}
    for row in receipt['modules']:
        assert row['kernel']=='replaying '+row['module'] and 'sorryAx' not in row['stdout']
    print(len(manifest['modules']), 'original source blobs,',len(wanted),'graph anchors,', len(checked),'kernel-replayed modules')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for field in ['repo','mathlib','graph']:p.add_argument('--'+field,type=Path)
    args=p.parse_args()
    verify(args.repo,args.mathlib,args.graph)
