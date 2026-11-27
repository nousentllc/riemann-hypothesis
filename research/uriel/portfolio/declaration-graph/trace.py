"""Replay the download checksum, edge counts and one shortest RH-to-sw_one path."""
from array import array
from collections import deque
from hashlib import sha256
import argparse
import gzip
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GRAPH = ROOT / 'alp-declaration-graph-used-by-rh.json.gz'
EXPECTED = '82c88d25d909a1399c754b87ce298e1939ab0908aeb4766fdac8a57387c71dc5'
SW = 'CompanionTheory.PlacePermOperatorBicommutantSpan.sw_one'
LOWER = 'GlobalTheory.T.exists_frequently_mul_pow_le_tprod_rank_one_local_density'
ERROR = 'GlobalTheory.T.thetaMeas_rank_one_sub_density_product_le'


def stream():
    with gzip.open(GRAPH, 'rb') as source:
        for line in source:
            if line.startswith(b'{"id":'):
                yield json.loads(line.rstrip().rstrip(b','))


def trace():
    h = sha256()
    with GRAPH.open('rb') as fp:
        for block in iter(lambda:fp.read(1<<20), b''):
            h.update(block)
    assert h.hexdigest() == EXPECTED
    edges = array('I')
    start = array('I', [0])
    keys = {}
    with gzip.open(GRAPH,'rt') as fp:
        meta=json.loads(fp.readline().strip().removesuffix(',')+'}')['meta']
    for row in stream():
        assert row['id'] == len(start)-1
        edges.extend(sorted(set(row['uses_in_signature']) | set(row['uses_in_body'])))
        start.append(len(edges))
        if row['name'] in ('riemannHypothesis',SW,LOWER,ERROR):
            keys[row['name']]=row['id']
    n=len(start)-1
    assert n==meta['declarations'] and len(edges)==meta['links']
    assert min(edges)>=0 and max(edges)<n
    origin, goal=keys['riemannHypothesis'],keys[SW]
    parent=array('i', [-1])*n
    parent[origin]=origin
    q=deque([origin])
    while q:
        a=q.popleft()
        if a==goal:break
        for b in edges[start[a]:start[a+1]]:
            if parent[b]<0:
                parent[b]=a
                q.append(b)
    path=[goal]
    while path[-1]!=origin:
        p=parent[path[-1]]
        assert p>=0
        path.append(p)
    path.reverse()
    wanted=set(path)|set(keys.values())
    data={row['id']:row for row in stream() if row['id'] in wanted}
    assert len(path)-1 == data[goal]['steps_below_riemannHypothesis']
    def node(idx):
        return {k:data[idx][k] for k in ('id','name','file','line','steps_below_riemannHypothesis')}
    def relation(a,b):
        return [k for k in ('uses_in_signature','uses_in_body') if b in data[a][k]]
    route=[dict(**node(i),outgoing_reference=relation(i,j)) for i,j in zip(path,path[1:])]
    route.append(node(goal))
    inputs=[dict(**node(keys[k]),reference_from_sw_one=relation(goal,keys[k])) for k in (ERROR,LOWER)]
    assert all('uses_in_body' in d['reference_from_sw_one'] for d in inputs)
    return dict(url='https://photos.proofsandreasons.io/alp-graph/rh/'+GRAPH.name,
                sha256=h.hexdigest(),publisher_metadata=meta,unique_directed_edges=len(edges),
                nodes=n,shortest_distance=len(path)-1,one_shortest_path=route,inputs=inputs)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true')
    out=ROOT/'sw_one_route.json'
    result=trace()
    body=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if p.parse_args().write: out.write_text(body)
    else: assert out.read_text()==body
    print(result['nodes'],result['unique_directed_edges'],result['shortest_distance'])
