"""Audit source identity, proof-excerpt provenance, the graph route and replay receipt."""
import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def load(file):
    return json.loads((ROOT / file).read_bytes())


def check(repo=None, graph=None):
    sources = load('sources.json')
    for entry in sources['files']:
        data = (ROOT / entry['local']).read_bytes()
        git_object = b'blob ' + str(len(data)).encode() + b'\0' + data
        assert hashlib.sha1(git_object).hexdigest() == entry['blob']
        assert hashlib.sha256(data).hexdigest() == entry['sha256']
        if repo:
            rev = sources['commit'] + ':' + entry['path']
            assert subprocess.check_output(['git','-C',repo,'rev-parse',rev]).decode().strip() == entry['blob']
    inputs = (ROOT/'verification/Inputs.lean').read_text()
    for name, where in [('two_le_norm','Growth'), ('exists_exponents','Growth'),
                        ('exists_den','Growth'), ('bound_step','Quad'),
                        ('summable_one_div_absNorm_sq','Summable')]:
        body = inputs.split('theorem '+name+' ',1)[1]
        end = min([len(body)] + [body.index(k) for k in ['\nend ', '\ntheorem '] if k in body])
        assert ('theorem '+name+' '+body[:end].rstrip()) in (ROOT/'source'/f'{where}.lean').read_text()
    receipt = load('verification/receipt.json')
    for module in receipt['modules']:
        path=ROOT/'verification'/Path(*module['module'].split('.')).with_suffix('.lean')
        assert hashlib.sha256(path.read_bytes()).hexdigest() == module['sha256']
        assert module['kernel'] == 'replaying '+module['module']
    for alias, module in zip(['NZ','EulerSum','Abs'],receipt['modules'][:3]):
        path=ROOT/'verification'/Path(*module['module'].split('.')).with_suffix('.lean')
        assert path.read_bytes() == (ROOT/'source'/f'{alias}.lean').read_bytes()
    record=load('graph.json')
    nodes=record['route']
    for a,b in zip(nodes,nodes[1:]):
        assert b['id'] in a['uses_in_body']
    original={e['path'].removeprefix('src/'):ROOT/e['local'] for e in sources['files']}
    for node in nodes:
        line=original[node['file']].read_text().splitlines()[node['line']-1]
        assert line.startswith('theorem ') and line.split()[1].split('.')[-1] == node['name'].split('.')[-1]
    if graph:
        with graph.open('rb') as fp: assert hashlib.file_digest(fp,'sha256').hexdigest()==record['sha256']
        wanted={v['id']:v for v in nodes}; seen=set()
        with gzip.open(graph,'rb') as fp:
            for line in fp:
                if not line.startswith(b'{"id":'): continue
                d=json.loads(line.rstrip().rstrip(b','))
                if d['id'] in wanted:
                    assert all(d[k]==v for k,v in wanted[d['id']].items())
                    seen.add(d['id'])
                    if len(seen)==len(wanted): break
        assert seen==set(wanted)
    print(len(sources['files']), 'source blobs, 5 verbatim declaration bodies, 5 module receipts, 3 original graph body edges')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--repo',type=Path)
    parser.add_argument('--graph',type=Path)
    args=parser.parse_args()
    check(args.repo,args.graph)
