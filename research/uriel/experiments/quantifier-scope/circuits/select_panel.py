"""Deterministically specify new topologies, physical thresholds, and observed lamps."""
import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import random
from network import all_states, network_edges

HERE=Path(__file__).resolve().parent
SIZES=[(7,17),(8,17),(9,16),(10,14),(10,15),(11,14)]


def trial_graph(n,m,rng):
    interior=list('abcdefghi'[:n-2])
    rng.shuffle(interior)
    path=['+',*interior,'0']
    edges=list(zip(path,path[1:]))
    used={frozenset(e) for e in edges}
    pool=[e for e in combinations(sorted(path),2) if frozenset(e) not in used and frozenset(e)!=frozenset('0+')]
    rng.shuffle(pool)
    edges.extend(pool[:m-len(edges)])
    parts=[]
    for j,(u,v) in enumerate(edges):
        if rng.randrange(2):
            u,v=v,u
        sw={m-3:'/s',m-2:'/t',m-1:'/u'}.get(j,'')
        parts.append(f'{u}/{v}/{rng.randrange(2,10)}{sw}')
    return ' '.join(parts)


def thresholds(vals):
    probes=[]
    for channel in vals[0]:
        readings=[x[channel] for x in vals]
        unique=sorted(set(readings))
        for lo,hi in zip(unique,unique[1:]):
            candidates={lo,(lo+hi)/2}
            for d in range(1,13):
                x=F(lo.numerator*d//lo.denominator+1,d)
                if x<hi:candidates.add(x)
            cut=min(candidates,key=lambda x:(len(str(x)),x.denominator,abs(x.numerator),x))
            mask=sum(1<<j for j,x in enumerate(readings) if x>cut)
            if mask.bit_count()==4:
                probes.append((channel,str(cut),mask))
    return probes


def choose(graph,family_index):
    edges=network_edges(graph)
    values=[v for _,v in all_states(edges)]
    probes=thresholds(values)
    best=None
    for target in probes:
        var,threshold,t=target
        if var[0]!='I':continue
        u,v,_,switch=edges[int(var[1:])-1]
        if switch!='-' or {u,v} & {'+','0'}:continue
        for initial in probes:
            if initial[0]==var:continue
            # The first observed lamp is balanced across families.
            initial_high=family_index in (0,3,4)
            cell=initial[2] if initial_high else initial[2]^255
            if (cell&t).bit_count()!=2:continue
            for decisive in probes:
                meter=decisive[2]
                if decisive[0] in (var,initial[0]):continue
                direct=family_index%2==0
                if (cell & (t if direct else t^255)) != (cell & meter):continue
                # Even in the full table, each forced reading by itself is ambiguous.
                if not all((q&t) and (q & ~t) for q in [meter,meter^255]):continue
                for distractor in probes:
                    noise=distractor[2]
                    if distractor[0] in (var,initial[0],decisive[0]):continue
                    if not all((q&t).bit_count()==1 and (q & ~t).bit_count()==1 for q in [cell&noise,cell&~noise]):continue
                    physical=[x[var] for x in values]
                    simple=sum(len(p[1]) for p in (target,initial,decisive,distractor))
                    rank=(min(physical)<0<max(physical),-simple)
                    if best is None or rank>best[0]:
                        best=(rank,dict(layout=graph,target=target[:2],initial=initial[:2],initial_reading='H' if initial_high else 'L',
                                decisive=decisive[:2],other=distractor[:2]))
    return best[1] if best else None


def construct():
    output={}
    for j,(n,m) in enumerate(SIZES):
        rng=random.Random(2026112473+j)
        for trial in range(200):
            g=trial_graph(n,m,rng)
            spec=choose(g,j)
            if spec:
                spec['selected_trial']=trial
                output[f'K{j+1}']=spec
                break
        else:raise ValueError(f'No admissible design for {(n,m)}')
    return output


if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--write',action='store_true')
    fresh=construct()
    path=HERE/'design.json'
    text=json.dumps(fresh,indent=2)+'\n'
    if a.parse_args().write:path.write_text(text)
    elif path.read_text()!=text:raise ValueError('Frozen layout differs')
    print({k:v['selected_trial'] for k,v in fresh.items()})
