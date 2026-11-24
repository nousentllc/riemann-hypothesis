"""How four explicit alternative comparison rules alter the sealed evidence panel."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "circuits"
RULES = {
    "registered_strict": lambda i, t: i > t,
    "inclusive": lambda i, t: i >= t,
    "absolute_current_signed_threshold": lambda i, t: abs(i) > t,
    "absolute_current_absolute_threshold": lambda i, t: abs(i) > abs(t),
    # Python round(Fraction) computes the nearest integer, breaking half-ties to even.
    "rounded_tenths_strict": lambda i, t: round(10*i) > round(10*t),
}


def sign(ids, truth):
    classes = {truth[x] for x in ids}
    if not classes:
        raise ValueError("Empty observation cell")
    return "U" if len(classes) == 2 else "Y" if True in classes else "N"


def certificates(ids, truth):
    answer = sign(ids, truth)
    if answer in ("Y", "N"):
        return {(answer, tuple(sorted(ids)))}
    return {("U", (a, b)) for a,b in combinations(sorted(ids), 2) if truth[a] != truth[b]}


def oracle(row, truth):
    ids = row["eligible"]
    before = sign(ids, truth)
    cells, guaranteed, actual_decisive = {}, [], []
    for meter in row["menu"]:
        groups = {}
        for reading in {"L", "H"}:
            survivors = [q for q in ids if row["states"][q]["obs"][meter] == reading]
            if survivors:
                groups[reading] = {"sign": sign(survivors, truth), "states": sorted(survivors)}
        cells[meter] = groups
        if before != "U":
            continue
        if all(g["sign"] != "U" for g in groups.values()):
            guaranteed.append(meter)
        lamp = row["states"][row["actual"]]["obs"][meter]
        if groups[lamp]["sign"] != "U":
            actual_decisive.append(meter)
    if before != "U":
        kind = "settled"
        strongest = before
    elif guaranteed:
        kind = "guaranteed_lookup"
        strongest = sign([row["actual"]], truth)
    elif actual_decisive:
        kind = "contingent_lookup"
        strongest = sign([row["actual"]], truth)
    else:
        kind = "ambiguous"
        strongest = "U"
    return {"initial": before, "kind":kind, "strongest_on_actual":strongest,
            "guaranteed": sorted(guaranteed), "decisive_on_actual": sorted(actual_decisive),
            "cells": cells}


def transitions(old, new):
    a = set(old["guaranteed"])
    b = set(new["guaranteed"])
    if new["kind"] == "settled":
        return "already_settled"
    if a == b:
        return "same_guaranteed_set"
    if a <= b:
        return "original_plus_another"
    if b and not a & b:
        return "different_guaranteed_meter"
    if not b:
        return "no_guaranteed_meter"
    raise ValueError("Unexpected transition from a single registered guaranteed meter")


def audit():
    raw = (SOURCE/"records.json").read_bytes()
    chk = json.loads((SOURCE/"verification.json").read_text())
    assert sha256(raw).hexdigest() == chk["sha256"]["records.json"]
    rows = json.loads(raw)
    unsigned_ties = [F(1,20),F(3,20),F(5,20),F(-1,20),F(-3,20),F(-5,20)]
    assert [round(10*v) for v in unsigned_ties] == [0,2,2,0,-2,-2]
    by_rule = {}
    for name, comparer in RULES.items():
        cases, changed_ids, families = {}, [], set()
        grouped_changes, control_loss_counts = Counter(), Counter()
        controls_any, controls_all, control_target_changes, lookup_target_changes = [], [], [], []
        for rid, row in rows.items():
            threshold = F(row["target_threshold"])
            original_truth = {i:s["answer"] for i,s in row["states"].items()}
            altered_truth = {i:comparer(F(s["target_current"]),threshold) for i,s in row["states"].items()}
            if row["family"] not in families:
                families.add(row["family"])
                for i,truth in original_truth.items():
                    if truth != altered_truth[i]:
                        changed_ids.append({"family":row["family"],"id":i,"current":row["states"][i]["target_current"],
                                            "threshold":str(threshold),"registered":truth,"altered":altered_truth[i]})
            original = oracle(row, original_truth)
            new = oracle(row, altered_truth)
            checked = chk["record_oracles"][rid]
            assert original["strongest_on_actual"] == checked["attainable"]
            assert original["guaranteed"] == sorted(checked["guaranteed"])
            assert original["kind"].replace("guaranteed_lookup", "lookup") == checked["kind"]
            old_certs = certificates(row["eligible"], original_truth)
            surviving = old_certs & certificates(row["eligible"], altered_truth)
            lost = old_certs - surviving
            change = None
            if original["kind"] == "guaranteed_lookup":
                change = transitions(original, new)
                grouped_changes[change] += 1
                if original["strongest_on_actual"] != new["strongest_on_actual"]:
                    lookup_target_changes.append(rid)
            else:
                if lost:
                    controls_any.append(rid)
                if not surviving:
                    controls_all.append(rid)
                if original["strongest_on_actual"] != new["strongest_on_actual"]:
                    control_target_changes.append(rid)
                control_loss_counts["original"] += len(old_certs)
                control_loss_counts["lost"] += len(lost)
                control_loss_counts["retained"] += len(surviving)
            cases[rid] = {"registered_initial":original["initial"],"registered_kind":original["kind"],
                          "registered_strongest":original["strongest_on_actual"],"registered_guaranteed":original["guaranteed"],
                          "altered":new, "meter_transition":change, "retained_initial_certificates":sorted(surviving),
                          "lost_initial_certificates":sorted(lost)}
        by_rule[name] = {"changed_physical_truths":len(changed_ids),"changed_settings":changed_ids,
                         "actionable_meter_transitions":dict(grouped_changes),
                         "actionable_changed_strongest":lookup_target_changes,
                         "control_any_certificate_lost":controls_any,"control_all_certificates_lost":controls_all,
                         "control_changed_strongest":control_target_changes,"control_certificate_counts":dict(control_loss_counts),
                         "records":cases}
    assert by_rule["registered_strict"]["changed_physical_truths"] == 0
    assert by_rule["registered_strict"]["actionable_meter_transitions"] == {"same_guaranteed_set":6}
    assert len(by_rule["inclusive"]["changed_settings"]) == chk["physical_checks"]["target_equalities"]
    return {"source_sha256":sha256(raw).hexdigest(), "protocol_sha256":sha256((HERE/"PROTOCOL.md").read_bytes()).hexdigest(),
            "rules":by_rule}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = audit()
    text = json.dumps(result, indent=2,sort_keys=True)+"\n"
    if args.write:
        (HERE/"results.json").write_text(text)
    elif text != (HERE/"results.json").read_text():
        raise ValueError("Archived alternative rules differ from recomputation.")
    for name, r in result["rules"].items():
        print(name,r["changed_physical_truths"],r["actionable_meter_transitions"],
              r["actionable_changed_strongest"],r["control_certificate_counts"],
              r["control_any_certificate_lost"],r["control_all_certificates_lost"],r["control_changed_strongest"])
