"""Validate circuit topology, every physical state, and every possible lookup outcome."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
from cases import build, row_ids, description
from network import NETWORKS, HISTORICAL_NETWORKS, network_edges, model

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


def graph_size(spec):
    edges = network_edges(spec)
    return len({v for u, w, *_ in edges for v in (u, w)}), len(edges)


def physical_audit(family, pair, specification, ids, counts):
    left, right = pair
    assert left["text"] == right["text"] and left["menu"] == right["menu"]
    assert left["states"] == right["states"] and left["target_threshold"] == right["target_threshold"]
    assert {left["evidence"], right["evidence"]} == {
        "The initial comparator reading is H.", "The initial comparator reading is L."}
    assert sorted(left["eligible"] + right["eligible"]) == sorted(left["states"])
    assert all(row["actual"] in row["eligible"] for row in pair)
    edges = network_edges(NETWORKS[family])
    assert sorted(sw for *_,sw in edges if sw != "-") == list("stu")
    for i, bit_tuple in enumerate(product((0, 1), repeat=3)):
        bits = dict(zip("stu", bit_tuple))
        volts, amps = model(edges, bits)
        independent = forest_voltages(edges, bits)
        assert volts == independent and all(0 <= v <= 12 for v in volts.values())
        recomputed = [(independent[u] - independent[v]) / r if s == "-" or bits[s] else F(0)
                      for u, v, r, s in edges]
        assert recomputed == amps
        residual = dict.fromkeys(volts, F(0))
        for (u, v, _, _), amperes in zip(edges, recomputed):
            residual[u] += amperes
            residual[v] -= amperes
        assert all(not residual[v] for v in set(volts) - {"+", "0"})
        assert sum(i*i*r for i, (_, _, r, _) in zip(recomputed, edges)) == 12 * residual["+"]
        counts.update({"switch_states": 1, "node_voltages": len(volts), "branch_currents": len(amps)})
        values = {"V"+n: v for n,v in independent.items()}
        values.update({"I"+str(j): value for j, value in enumerate(recomputed, 1)})

        def lamp(probe):
            variable, threshold = probe
            return "H" if values[variable] > F(threshold) else "L"

        rid = ids[i]
        state = left["states"][rid]
        tabrow = [ln.split() for ln in left["text"].splitlines() if ln.startswith(rid+" ")]
        var, threshold = specification["target"]
        assert len(tabrow) == 1
        cells = tabrow[0]
        assert cells[1] == state["bits"] == "".join(map(str, bit_tuple))
        assert cells[2] == state["target_current"] == str(values[var])
        assert left["target_threshold"] == threshold
        assert type(state["answer"]) is bool and state["answer"] == (lamp(specification["target"]) == "H")
        counts["target_equalities"] += values[var] == F(threshold)
        counts["negative_target_currents"] += values[var] < 0
        assert cells[3] == state["initial"] == lamp(specification["observed"])
        for row in pair:
            assert (rid in row["eligible"]) == (row["evidence"] == f"The initial comparator reading is {cells[3]}.")
        for col, (name, probe) in enumerate(zip(left["menu"], specification["menu"]), 4):
            assert left["menu"][name] == description(probe)
            assert cells[col] == state["obs"][name] == lamp(probe)
            counts["menu_predictions"] += 1


def classify(row):
    eligible = row["eligible"]
    states = row["states"]
    actual = row["actual"]

    def signs(cell):
        return {states[v]["answer"] for v in cell}

    lamps = {}
    for meter in row["menu"]:
        groups = {}
        for lamp in ("L", "H"):
            cell = [v for v in eligible if states[v]["obs"][meter] == lamp]
            if cell:
                signed = signs(cell)
                groups[lamp] = {"states": cell, "sign": "U" if len(signed) > 1 else "Y" if True in signed else "N"}
        lamps[meter] = groups
    guaranteed = [k for k, g in lamps.items() if all(cell["sign"] != "U" for cell in g.values())]
    varies = [k for k, g in lamps.items() if len(g) == 2]
    if len(signs(eligible)) == 1:
        kind = "settled"
        assert len(guaranteed) == 3
    elif guaranteed:
        kind = "lookup"
        assert len(guaranteed) == 1 and len(varies) >= 2
        assert {group["sign"] for group in lamps[guaranteed[0]].values()} == {"N","Y"}
        for meter, groups in lamps.items():
            if meter not in guaranteed:
                assert all(cell["sign"] == "U" for cell in groups.values())
    else:
        kind = "ambiguous"
        assert varies
        assert all(cell["sign"] == "U" for groups in lamps.values() for cell in groups.values())
    return {"kind": kind, "attainable": "U" if kind == "ambiguous" else "Y" if states[actual]["answer"] else "N",
            "eligible": eligible, "actual": actual, "guaranteed": guaranteed if kind == "lookup" else [],
            "varying_meters": varies, "all_possible_replies": lamps}


def audit():
    frozen = json.loads((HERE/"records.json").read_text())
    assert build() == frozen and len(frozen) == 12
    specs = json.loads((HERE/"design.json").read_text())
    assert set(specs) == set(NETWORKS)
    ids = row_ids()
    counts = Counter()
    old_fingerprint = sha256(json.dumps(HISTORICAL_NETWORKS,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    assert old_fingerprint == "a5e8160bfabf4d24c9448421ebea122db7ff6cda00a422571a5c5a73e8fc2b75"
    old_sizes = {k: graph_size(layout) for k, layout in HISTORICAL_NETWORKS.items()}
    sizes = {k: graph_size(layout) for k, layout in NETWORKS.items()}
    assert len(set(sizes.values())) == 6 and set(sizes.values()).isdisjoint(old_sizes.values())
    assert len({rid for labels in ids.values() for rid in labels}) == 48
    outcomes, kinds, positions = {}, Counter(), Counter()
    for family, spec in specs.items():
        pair = [(k,row) for k,row in frozen.items() if row["family"] == "DC-"+family]
        assert len(pair)==2 and {r["variant"] for _,r in pair} == {"1","2"}
        physical_audit(family, [row for _,row in pair], spec, ids[family], counts)
        family_classes = []
        for key, row in pair:
            info = classify(row)
            outcomes[key] = info
            family_classes.append(info["kind"])
            kinds[(info["kind"],info["attainable"])] += 1
            assert len(info["eligible"]) == 4
            if info["kind"] == "lookup":
                position = list(row["menu"]).index(info["guaranteed"][0]) + 1
                positions[position] += 1
        assert sorted(family_classes) in [["ambiguous","lookup"],["lookup","settled"]]
    assert kinds == Counter({("lookup","Y"):3, ("lookup","N"):3, ("settled","Y"):2, ("settled","N"):1,
                              ("ambiguous","U"):3})
    assert positions == {1:2,2:2,3:2}
    return {"topology_invariant":"vertex count, edge count including each separately controllable resistor",
            "historical_topologies":old_sizes, "fresh_topologies":sizes, "physical_checks":dict(counts),
            "reachable_lookup_cells":sum(len(c) for i in outcomes.values() for c in i["all_possible_replies"].values()),
            "record_classes":{"/".join(k):v for k,v in sorted(kinds.items())},
            "guaranteed_position_counts":dict(positions), "record_oracles":outcomes,
            "sha256":{f:sha256((HERE/f).read_bytes()).hexdigest() for f in
                      ("cases.py","network.py","design.json","records.json","check.py")}}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Archive reference results in verification.json.")
    args = parser.parse_args()
    report = audit()
    encoded = json.dumps(report, indent=2, ensure_ascii=False)+"\n"
    if args.write:
        (HERE/"verification.json").write_text(encoded)
    elif encoded != (HERE/"verification.json").read_text():
        raise RuntimeError("Results differ from archived independent verification")
    print(json.dumps({k:v for k,v in report.items() if k in ("physical_checks","record_classes","reachable_lookup_cells","guaranteed_position_counts")}, indent=2))
