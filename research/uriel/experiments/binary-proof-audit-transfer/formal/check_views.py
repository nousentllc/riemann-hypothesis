"""Recompute every public meter and initial observation from the candidate parameters."""
import re
from cases import FAMILIES, catalog, records


def public_values(family, raw):
    if family == 'unions':
        left, right = [frozenset(s) for s in raw]
        return len(left), (len(right), 0 in left, 3 in right)
    if family == 'determinants':
        a,b,c,d = raw
        return a,(b,c,(d//2)*2==d)
    if family == 'neighbors':
        adjacency={v:set() for v in range(5)}
        for a,b in raw:
            adjacency[a].add(b)
            adjacency[b].add(a)
        return sum(map(len,adjacency.values()))//2,(len(adjacency[0]),len(adjacency[3]),2 in adjacency[0])
    if family == 'quadratics':
        a,b,c=raw
        return a, (max(b,-b),2*(c//2)==c,b>=1)
    if family == 'swaps':
        image=0
        for a,b in reversed(raw):
            if image==a: image=b
            elif image==b: image=a
        return raw[0][0], (image==0,raw[1][0],raw[2][1]==2)
    if family == 'hamming':
        x,y,z=map(lambda s:list(map(int,s)),raw)
        return sum(x),(y[0],z[-1],sum(z))
    if family == 'pairs-in-bins':
        left,right=raw
        return left-2*(left//2),(right-2*(right//2),right>=4,left>=4)
    if family == 'pair-encoding':
        a,b,c,d=raw
        return a,(c, b<1, d==2)
    raise ValueError(family)


def audit_views():
    checks=0
    for family in FAMILIES:
        for row in records(family):
            readings={}
            initial={}
            for group,_ in catalog(family):
                for candidate in group:
                    candidate_id=next(line.split(':',1)[0] for line in row['text'].splitlines()
                                      if line.endswith(': '+candidate.description+'.'))
                    i,obs=public_values(family.name,candidate.raw)
                    initial[candidate_id]=str(i)
                    readings[candidate_id] = {item: str(int(obs[family.menu_labels.index(label)]))
                                              for item,label in row['menu'].items()}
            value=re.fullmatch(r'The .+ is (\d+)\.',row['evidence']).group(1)
            assert initial[row['actual']]==value
            assert set(row['eligible'])=={s for s in initial if initial[s]==value}
            assert all(v==row['states'][s]['obs'] for s,v in readings.items())
            checks+=1
    return checks


if __name__=='__main__':
    print(f"{audit_views()} full public model tables and initial evidence records checked.")
