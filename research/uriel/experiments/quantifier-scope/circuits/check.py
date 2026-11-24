"""Independent two-root-forest solution and exhaustive joint-compatibility audit."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations,product
import json
from pathlib import Path
from cases import build,probe_description
from network import HISTORICAL_NETWORKS,PREVIOUS_THRESHOLD_NETWORKS,PREVIOUS_FORCED_NETWORKS,PREVIOUS_MARKED_NETWORKS,PREVIOUS_LABEL_NETWORKS,network_edges,model

HERE=Path(__file__).resolve().parent

def forest_voltages(edges, bits):
    """Independent 2-root forest enumeration (Dirichlet voltage representation)."""
    nodes = {n for u,v,_,_ in edges for n in [u,v]}
    active = [(u,v,F(1,r)) for u,v,r,s in edges if s=="-" or bits[s]]
    total = F(0)
    pos = dict.fromkeys(nodes,F(0))
    for subset in combinations(active, len(nodes)-2):
        labels = {v:v for v in nodes}
        weight = F(1)
        for u,v,g in subset:
            i,j=labels[u],labels[v]
            if i==j: break
            labels={x:(i if y==j else y) for x,y in labels.items()}
            weight *= g
        else:
            if labels["+"]==labels["0"]:continue
            total += weight
            for x in nodes:
                if labels[x]==labels["+"]: pos[x] += weight
    assert total > 0
    return {x:12*w/total for x,w in pos.items()}

def graph_size(spec):
    edges = network_edges(spec)
    return len({v for u, w, *_ in edges for v in (u, w)}), len(edges)


def audit():
    specs=json.loads((HERE/'design.json').read_text()); rows=json.loads((HERE/'records.json').read_text())
    assert rows==build() and len(rows)==24 and len(specs)==6
    old={**HISTORICAL_NETWORKS,**PREVIOUS_THRESHOLD_NETWORKS,**PREVIOUS_FORCED_NETWORKS,**PREVIOUS_MARKED_NETWORKS,**PREVIOUS_LABEL_NETWORKS}
    old_shapes={k:graph_size(s) for k,s in old.items()}
    assert len(old_shapes)==32
    new_shapes={k:graph_size(s['layout']) for k,s in specs.items()}
    assert len(set(new_shapes.values()))==6 and not set(new_shapes.values())&set(old_shapes.values())
    phys=Counter(); outcomes={}; family_out={}; unique_ids=set()
    for family,spec in specs.items():
        keys=[k for k,r in rows.items() if r['family']=='DC-'+family]
        assert len(keys)==4
        row=rows[keys[0]]; edges=network_edges(spec['layout']); states=row['states']
        assert len(states)==8 and len(set(row['state_order']))==8 and set(row['state_order'])==states.keys()
        assert not unique_ids & states.keys()
        unique_ids.update(states)
        by_bits={s['bits']:sid for sid,s in states.items()}
        assert sorted(by_bits)==[''.join(map(str,b)) for b in product((0,1),repeat=3)]
        assert len({frozenset((u,v)) for u,v,_,_ in edges})==len(edges)
        assert sorted(sw for *_,sw in edges if sw!='-')==list('stu')
        target=spec['target']; assert row['target_threshold']==target[1] and row['signed_branch']=='R'+target[0][1:]
        menu_types={probe_description(spec[p]):spec[p] for p in ('other','decisive')}
        assert len(menu_types)==2 and set(row['menu'].values())==menu_types.keys()
        assert row['initial_description']==probe_description(spec['initial'])
        for bits,identifier in by_bits.items():
            switches={n:int(b) for n,b in zip('stu',bits)}
            volt,amps=model(edges,switches)
            v=forest_voltages(edges,switches)
            assert volt==v and all(0<=x<=12 for x in v.values())
            independent=[(v[u]-v[w])/r if sw=='-' or switches[sw] else F(0) for u,w,r,sw in edges]
            assert amps==independent
            balan=dict.fromkeys(v,F(0))
            for (u,w,_,_),x in zip(edges,independent):
                balan[u]+=x;balan[w]-=x
            assert all(balan[u]==0 for u in set(v)-{'+','0'})
            assert 12*balan['+']==sum(x*x*r for x,(_,_,r,_) in zip(independent,edges))
            variables={'I'+str(k):x for k,x in enumerate(independent,1)}
            variables.update({'V'+u:n for u,n in v.items()})
            def lamp(probe):return 'H' if variables[probe[0]]>F(probe[1]) else 'L'
            state=states[identifier]
            assert state['initial']==lamp(spec['initial'])
            assert type(state['answer']) is bool and state['answer']==(lamp(target)=='H')
            assert str(variables[target[0]])==state['target_current']
            assert state['obs']=={m:lamp(menu_types[name]) for m,name in row['menu'].items()}
            phys.update({'switch_states':1,'node_voltages':len(v),'branch_currents':len(independent),
                'target_current_equal_to_threshold':int(variables[target[0]]==F(target[1])),
                'negative_target_current':int(variables[target[0]]<0),'meter_predictions':len(row['menu'])})
        group={}
        for k in keys:
            r=rows[k]
            for common in ('states','target_threshold','signed_branch','initial_description','initial_reading','menu','state_order','description'):
                assert r[common]==row[common],(family,common)
            pos={s for s,d in states.items() if d['answer']}
            assert len(pos)==4
            i=r['initial_reading'];m=r['meter'];w=r['reading']
            start={s for s,d in states.items() if d['initial']==i}
            meter_alone={s for s,d in states.items() if d['obs'][m]==w}
            end=start & meter_alone
            assert len(start)==4 and len(start & pos)==2 and len(meter_alone)==4 and 0<len(meter_alone & pos)<4
            assert len(end)==2 and r['eligible']==[s for s in r['state_order'] if s in start]
            assert r['survivors']==[s for s in r['state_order'] if s in end]
            n=len(end & pos)
            verdict='U' if n==1 else 'Y' if n==2 else 'N'
            assert r['kind']==('ambiguous' if verdict=='U' else 'decisive')
            by_reply={}
            for lamp_value in ('L','H'):
                cell={s for s in start if states[s]['obs'][m]==lamp_value}
                assert len(cell)==2
                signs={states[s]['answer'] for s in cell}
                by_reply[lamp_value]=dict(ids=sorted(cell),verdict='U' if len(signs)==2 else 'Y' if True in signs else 'N')
            assert (r['kind']=='decisive')==(by_reply['L']['verdict']!='U' and by_reply['H']['verdict']!='U')
            if r['kind']=='ambiguous':
                assert by_reply['L']['verdict']==by_reply['H']['verdict']=='U'
            outcomes[k]=dict(family=r['family'],kind=r['kind'],verdict=verdict,initial=sorted(start),meter_alone=sorted(meter_alone),
                         joint=sorted(end),meter=m,reading=w,both_possible_replies=by_reply)
            group[k]=verdict
        assert Counter(group.values())=={'Y':1,'N':1,'U':2}
        for kind in ('decisive','ambiguous'):
            twin=[rows[k] for k in keys if rows[k]['kind']==kind]
            assert len(twin)==2 and twin[0]['meter']==twin[1]['meter']
            assert {t['reading'] for t in twin}=={'L','H'}
            a,b=(set(t['survivors']) for t in twin)
            assert a.isdisjoint(b) and (a|b)==set(row['eligible'])
        assert len({rows[k]['meter'] for k in keys})==2
        assert len({frozenset(rows[k]['survivors']) for k in keys})==4
        h=next(group[k] for k in keys if rows[k]['kind']=='decisive' and rows[k]['reading']=='H')
        family_out[family]=dict(shape=list(new_shapes[family]),H_means=h,records=group)
    assert Counter(v['H_means'] for v in family_out.values())=={'N':3,'Y':3}
    assert len(unique_ids)==48
    historical=json.loads((HERE/'historical_ids.json').read_text())
    assert set(historical)==set(old_shapes)
    prior_ids={x for ids in historical.values() for x in ids}
    assert len(prior_ids)==256 and not (unique_ids & prior_ids)
    files=('historical_ids.json','network.py','select_panel.py','cases.py','design.json','records.json','check.py')
    return dict(previous_graph_sizes=old_shapes,new_graph_sizes=new_shapes,physical_checks=dict(phys),
                previous_unique_state_ids=len(prior_ids),new_unique_state_ids=len(unique_ids),
                H_to_Y=3,H_to_N=3,record_counts=dict(Counter(r['verdict'] for r in outcomes.values())),
                initial_count=4,one_forced_lamp_alone_count=4,intersection_count=2,all_one_lamp_truths_mixed=True,
                families=family_out,records=outcomes,sha256={name:sha256((HERE/name).read_bytes()).hexdigest() for name in files})


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--write',action='store_true')
    res=audit(); txt=json.dumps(res,indent=2)+'\n'
    if p.parse_args().write:(HERE/'verification.json').write_text(txt)
    elif (HERE/'verification.json').read_text()!=txt:raise ValueError('Archived verification differs')
    print(json.dumps({k:res[k] for k in ('physical_checks','record_counts','H_to_Y','H_to_N')},indent=2))
