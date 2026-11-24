"""Recompute the entire eight-state physical model using only the archived prompt text."""
from fractions import Fraction as F
from itertools import product
import argparse
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent


def solve(edges, word):
    active=[(u,v,F(1,int(r)) if not sw or word['stu'.index(sw)]=='1' else F(0)) for u,v,r,sw in edges]
    nodes=sorted({n for u,v,g in active for n in (u,v)}-{'0','+'})
    fixed={'0':F(0),'+':F(12)}
    mat=[[F(0) for i in range(len(nodes)+1)] for n in nodes]
    for a,b,g in active:
        for u,v in ((a,b),(b,a)):
            if u in fixed:
                continue
            i=nodes.index(u);mat[i][i]+=g
            if v in fixed: mat[i][-1]+=g*fixed[v]
            else: mat[i][nodes.index(v)]-=g
    for i in range(len(nodes)):
        j=next(j for j in range(i,len(nodes)) if mat[j][i])
        mat[i],mat[j]=mat[j],mat[i]
        div=mat[i][i];mat[i]=[n/div for n in mat[i]]
        for j in range(len(nodes)):
            if j!=i:
                fac=mat[j][i];mat[j]=[n-fac*p for n,p in zip(mat[j],mat[i])]
    volt=dict(fixed,**dict(zip(nodes,[row[-1] for row in mat])))
    currents={'R'+str(i):g*(volt[u]-volt[v]) for i,(u,v,g) in enumerate(active,1)}
    for n in nodes:
        assert sum((int(n==u)-int(n==v))*currents['R'+str(i)] for i,(u,v,g) in enumerate(active,1))==0
    return volt,currents


def compare(clause,volt,amps):
    mode,target,cut=re.fullmatch(r'(signed current of|voltage at) (\w+) > ([-\d/]+) [AV]',clause).groups()
    value=(amps if mode.startswith('signed') else volt)[target]
    return 'H' if value>F(cut) else 'L'


def reconstruct(row):
    lines=row['requests']['any']['messages'][1]['content'].splitlines()
    edges=re.findall(r'R\d+=([^> ]+)>([^: ]+):(\d+)(?:\[([stu])\])?',lines[0])
    target,cut=re.search(r'current of (R\d+) > ([-\d/]+) A',lines[1]).groups()
    initial=lines[2].split(': ',1)[1]
    menu=dict(x.split(': ',1) for x in lines[3].split(': ',1)[1].split(' | '))
    given={line.split()[1]:line.split() for line in lines[6:8]}
    ini,meter,value=re.search(r'initial = (\w); (M\d+) = (\w)',lines[-3]).groups()
    states={};eligible=[]
    for flags in product('01',repeat=3):
        word=''.join(flags)
        v,a=solve(edges,word)
        lamp=compare(initial,v,a)
        probes={m:compare(rule,v,a) for m,rule in menu.items()}
        label='Y' if a[target]>F(cut) else 'N'
        if lamp==ini and probes[meter]==value:eligible.append(word)
        states[word]=dict(target=str(a[target]),margin=str(a[target]-F(cut)),label=label,initial=lamp,meters=probes)
        if word in given:
            sid,bits,current,first,*rest=given[word]
            assert (F(current),first,rest)==(a[target],lamp,[*probes.values(),label])
    assert set(eligible)==set(given)
    return dict(edge_count=len(edges),threshold=cut,target=target,meter=meter,readings=ini+value,
                id_to_word={line[0]:word for word,line in given.items()},states=states)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    panel=json.loads((ROOT/'panel.json').read_text())
    data={rid:reconstruct(v) for rid,v in panel.items()}
    rendered=json.dumps(data,indent=2)+'\n'
    path=ROOT/'physics.json'
    if parser.parse_args().write: path.write_text(rendered)
    else: assert path.read_text()==rendered
    print('Verified all 8 switch settings per record, both displayed rows and their signed thresholds on all 12 records.')
