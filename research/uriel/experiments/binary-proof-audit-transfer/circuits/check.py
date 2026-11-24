"""Validate circuit topology, every physical state, and every possible lookup outcome."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
from cases import build, row_ids, description
from network import NETWORKS, network_edges, model

HERE = Path(__file__).resolve().parent


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


def truth_set(eligible,states):
    return {states[i]["answer"] for i in eligible}


def audit():
    rows = build()
    specs = json.loads((HERE/"design.json").read_text())
    passports, voltage_count, current_count, state_count = set(),0,0,0
    all_ids = set()
    all_sent = 0
    receipt = {"methods":["exact rational nodal elimination",
                          "independent positive two-root spanning forest sum",
                          "signed Kirchhoff residual, power conservation, packet reconstruction"]}
    ids=row_ids()
    for family,layout in NETWORKS.items():
        edges=network_edges(layout)
        nodes={x for u,v,_,_ in edges for x in (u,v)}
        passport=(len(nodes),len(edges))
        assert passport not in passports,(family,passport)
        passports.add(passport)
        frame_rows = [r for split in rows.values() for r in split if r["family"]=="DC-"+family]
        assert len(frame_rows)==2
        left,right=frame_rows
        assert left["text"]==right["text"] and left["menu"]==right["menu"]
        assert left["evidence"]!=right["evidence"] and set(left["eligible"]).isdisjoint(right["eligible"])
        assert not all_ids.intersection(left["states"]);all_ids.update(left["states"])
        for i,bits in enumerate(product((0,1),repeat=3)):
            sw=dict(zip("stu",bits))
            volts,amps=model(edges,sw)
            cross=forest_voltages(edges,sw)
            assert volts==cross
            voltage_count += len(volts)
            current_count += len(amps)
            state_count += 1
            independent=[((cross[u]-cross[v])/r if s=="-" or sw[s] else F(0))
                         for u,v,r,s in edges]
            assert independent==amps
            flux=dict.fromkeys(nodes,F(0))
            for amperes,(u,v,r,s) in zip(amps,edges):
                flux[u]+=amperes
                flux[v]-=amperes
            assert all(flux[x]==0 for x in nodes-{"+","0"})
            assert sum(c*c*r for c,(_,_,r,_) in zip(amps,edges))==12*flux["+"]
            assert all(0<=v<=12 for v in cross.values())
            readings={"V"+x:v for x,v in cross.items()}
            readings.update({"I"+str(j):v for j,v in enumerate(independent,1)})
            spec=specs[family]
            def reading(probe):
                q,t=probe
                return readings[q]>F(t)
            rid=ids[family][i]
            actual_answers=left["states"][rid]
            assert actual_answers["answer"]==reading(spec["target"])
            assert left["evidence"] == "The initial comparator reading is " + (
                ("H" if reading(spec["observed"]) else "L") if rid in left["eligible"]
                else ("L" if reading(spec["observed"]) else "H")) + "."
            state_lines = [s for s in left["text"].splitlines() if s.startswith(rid+" ")]
            assert len(state_lines)==1
            tokens=state_lines[0].split()
            assert tokens[1]==''.join(map(str,bits)) and F(tokens[2])==readings[spec["target"][0]]
            assert tokens[3]==("H" if reading(spec["observed"]) else "L")
            for j,(name,probe) in enumerate(zip(left["menu"],spec["menu"])):
                expected="H" if reading(probe) else "L"
                assert left["menu"][name]==description(probe)
                assert actual_answers["obs"][name]==tokens[4+j]==expected
                all_sent+=1
    receipt.update(network_topologies=len(passports),switch_states=state_count,
                   node_voltages_verified=voltage_count,branch_currents_verified=current_count,
                   packet_menu_predictions_verified=all_sent,distinct_state_labels=len(all_ids))
    splits={}
    for kind,stream in rows.items():
        counts=Counter()
        possible=0
        for row in stream:
            states=row["states"];initial=row["eligible"]
            assert row["actual"] in initial
            initial_truth=truth_set(initial,states)
            cases=[]
            for key in row["menu"]:
                reply=states[row["actual"]]["obs"][key]
                cell=[i for i in initial if states[i]["obs"][key]==reply]
                by_reply=[[i for i in initial if states[i]["obs"][key]==value] for value in ("H","L")]
                actual_truth=truth_set(cell,states)
                cases.append((len(actual_truth)==1,by_reply))
                for group in by_reply:
                    if group:
                        possible += 1
            if len(initial_truth)==1:
                typ="settled"
            elif any(z for z,_ in cases):
                typ="lookup"
                assert sum(z for z,_ in cases)==1
                for z,groups in cases:
                    if z:
                        assert all(len(truth_set(group,states))==1 for group in groups)
            else:
                typ="open"
                for _,groups in cases:
                    assert all(not g or truth_set(g,states)=={True,False} for g in groups)
            label=typ if typ=="open" else typ+"_"+str(states[row["actual"]]["answer"]).lower()
            counts[label]+=1
        splits[kind]={"families":len({r["family"] for r in stream}),"records":len(stream),
                      "classes":dict(sorted(counts.items())),"reachable_lookup_cells":possible}
    assert splits["test"]["classes"]=={"lookup_false":2,"lookup_true":2,"open":4,"settled_false":2,"settled_true":2}
    receipt["splits"]=splits
    receipt["code_hashes"]={f:sha256((HERE/f).read_bytes()).hexdigest()
                            for f in ("network.py","cases.py","design.json","check.py")}
    return receipt


if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
