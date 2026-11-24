"""Independent audit of the held-out menu-only revision, including every possible oracle response."""
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path

from cases import FAMILIES, build as original, catalog
from check_views import public_values
from score_cases import build as revised

HERE=Path(__file__).resolve().parent


def replacement(name, raw):
    if name=='unions': return len(set(raw[0]) & {3})
    if name=='neighbors': return len({v if u==2 else u for u,v in raw if 2 in (u,v)})>=3
    if name=='quadratics': return raw[2] > 4
    if name=='hamming': return sum(map(int,raw[1])) == 1
    raise ValueError(name)


def partition(states, eligible, item):
    cells=defaultdict(list)
    for s in eligible: cells[states[s]['obs'][item]].append(s)
    return dict(cells)


def row_kind(bits,decisive):
    if len(bits)==1: return 'settled'
    return 'lookup' if decisive else 'ambiguous'


def validate():
    old,new=original(),revised()
    assert old['dev']==new['dev']
    families={f.name:f for f in FAMILIES}
    counts=Counter()
    rows=[]
    for baseline,row in zip(old['test'],new['test'],strict=True):
        name=row['family']
        family=families[name]
        assert {k:v for k,v in baseline.items() if k not in ('menu','states')} == {
            k:v for k,v in row.items() if k not in ('menu','states')}
        assert baseline['states'].keys()==row['states'].keys()
        for group,_ in catalog(family):
            for candidate in group:
                s=next(line.split(':',1)[0] for line in row['text'].splitlines()
                       if line.endswith(': '+candidate.description+'.'))
                assert baseline['states'][s]['answer']==row['states'][s]['answer']==candidate.outcome
                _, values=public_values(name,candidate.raw)
                for item,label in row['menu'].items():
                    value=(values[family.menu_labels.index(label)] if label in family.menu_labels
                           else replacement(name,candidate.raw))
                    assert row['states'][s]['obs'][item]==str(int(value))
        states=row['states']
        es=row['eligible']
        bits={states[s]['answer'] for s in es}
        ac=row['actual']
        partitions={item:partition(states,es,item) for item in row['menu']}
        resolved=lambda ids:len({states[s]['answer'] for s in ids})==1
        varied=[item for item,part in partitions.items() if len(part)>1]
        guaranteed=[item for item,part in partitions.items() if all(map(resolved,part.values()))]
        decisive=[item for item,part in partitions.items() if resolved(part[states[ac]['obs'][item]])]
        kind=row_kind(bits,decisive)
        assert kind==family.designs[int(row['variant'])-1][0]
        if kind=='lookup': assert len(varied)==2 and len(guaranteed)==1 and guaranteed==decisive
        if kind=='ambiguous':
            assert all(any(states[s]['answer']!=states[t]['answer'] and states[s]['obs']==states[t]['obs'] for s in es) for t in es)
        counts[(kind,states[ac]['answer'])]+=1
        rows.append(dict(family=name,variant=row['variant'],type=kind,varies=varied,guarantees=guaranteed,
                    decisive_on_designated_object=decisive,partitions=partitions))
    assert len(counts)==6 and all(v==2 for v in counts.values())
    return dict(status='passed',dev_byte_equivalence=canonical(old['dev'])==canonical(new['dev']),
                original_dev_hash=canonical(old['dev']), scored_input_hash=canonical(new['test']),
                sources_and_finite_object_truths='same as original receipt.json',
                formal_scored_records=len(rows),rows=rows)


def canonical(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


if __name__=='__main__':
    result=validate()
    (HERE/'score_menu_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Scored menus verified; every alternative sensor response enumerated.')
