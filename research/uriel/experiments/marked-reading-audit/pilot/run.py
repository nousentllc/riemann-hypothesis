"""Freeze, verify, and collect a paired three-display panel."""
import argparse
import fcntl
from itertools import permutations
import json
import random

from instrument import (HERE, ROOT, MODEL, SERVER, TIMEOUT_SECONDS, digest, hash_request,
                        now, request_payload, save, stage, verify_model)

SEED = 2026112449
ARMS = ("unmarked","marked","filtered")
RECORDS = ROOT / "circuits" / "records.json"


def load(path):
    return json.loads(path.read_bytes())


def survivors(row):
    return {sid for sid,state in row["states"].items()
            if state["initial"] == row["initial_reading"] and state["obs"][row["meter"]] == row["reading"]}


def render(row, arm):
    if arm not in ARMS:
        raise ValueError(arm)
    meters = list(row["menu"])
    lines = [
        row["description"],
        f"Question: is the signed current of {row['signed_branch']} > {row['target_threshold']} A?",
        "Initial comparator: " + row["initial_description"],
        "Other comparators: " + " | ".join(f"{k}: {row['menu'][k]}" for k in meters),
        "H means a comparator condition holds and L means it fails. All currents are exact amperes. The last column gives the result of the named current comparison in each setting.",
        "In the mark column, * explicitly identifies a setting compatible with both observed readings. A dot means no marker is supplied for that row.",
        "mark ID stu target_current initial " + " ".join(meters) + " target_current_above_threshold",
    ]
    kept = survivors(row)
    for sid in row["state_order"]:
        if arm == "filtered" and sid not in kept:
            continue
        state = row["states"][sid]
        marker = "*" if arm == "marked" and sid in kept else "."
        lines.append(" ".join([marker,sid,state["bits"],state["target_current"],state["initial"],
                               *(state["obs"][m] for m in meters),"Y" if state["answer"] else "N"]))
    lines.extend(["",f"Observed readings: initial = {row['initial_reading']}; {row['meter']} = {row['reading']}.",
        "The table includes every setting compatible with both readings. Use both readings when identifying which settings remain possible.",
        "Y means the named claim holds in every compatible setting. N means it fails in every compatible setting. U means both answers are possible.",
        "For Y or N, list all and only the compatible IDs. For U, list exactly two compatible IDs with opposite target answers. Use no duplicate IDs.",
        "Both readings have already been supplied. Return only the JSON fields verdict and certificate."])
    return "\n".join(lines)


def schedule(rows):
    rng = random.Random(SEED)
    families = sorted({r["family"] for r in rows.values()})
    rng.shuffle(families)
    orders = list(permutations(ARMS))
    slots = sorted({(r["kind"],r["reading"]) for r in rows.values()})
    by_key = {(r["family"],r["kind"],r["reading"]):rid for rid,r in rows.items()}
    waves = [[],[],[]]
    for i,family in enumerate(families):
        for j,(kind,reading) in enumerate(slots):
            rid = by_key[family,kind,reading]
            order = orders[(i+j)%6]
            for wave,arm in zip(waves,order):
                wave.append(dict(record=rid,arm=arm))
    for wave in waves:
        rng.shuffle(wave)
    return [item for wave in waves for item in wave]


def payload_for(rid, arm, rows):
    prompt = (HERE/"prompts"/f"{rid}.{arm}.txt").read_text()
    messages = [dict(role="system",content=(HERE/"method.txt").read_text().strip()),
                dict(role="user",content=prompt)]
    return request_payload(messages,rows[rid],SEED+sorted(rows).index(rid))


def check_panel(rows):
    families = {r["family"] for r in rows.values()}
    if len(rows) != 24 or len(families) != 6:
        raise ValueError("Expected 24 records on six layouts")
    for family in families:
        quartet = [r for r in rows.values() if r["family"] == family]
        if {(r["kind"],r["reading"]) for r in quartet} != {(k,m) for k in ("decisive","ambiguous") for m in ("H","L")}:
            raise ValueError("Expected all four record types")
        for kind in ("decisive","ambiguous"):
            pair = [r for r in quartet if r["kind"] == kind]
            if (len({(r["meter"],r["initial_reading"]) for r in pair}) != 1
                    or not survivors(pair[0]).isdisjoint(survivors(pair[1]))):
                raise ValueError("Twins need same meter, opposite replies and disjoint witnesses")
    for rid,row in rows.items():
        kept = survivors(row)
        labels = {row["states"][sid]["answer"] for sid in kept}
        if (len(row["states"]) != 8 or len(kept) != 2 or kept != set(row["survivors"])
                or (len(labels) == 2) != (row["kind"] == "ambiguous")):
            raise ValueError(f"Invalid record {rid}")


def verify_frozen():
    registry = load(HERE/"freeze.json")
    for name,value in registry["sha256"].items():
        if digest(ROOT/name) != value:
            raise ValueError(f"Frozen artifact changed: {name}")
    return registry


def freeze():
    path = HERE/"freeze.json"
    if path.exists() or (HERE/"observed").exists():
        raise ValueError("Existing freeze or collection")
    verify_model()
    rows = load(RECORDS)
    check_panel(rows)
    dest = HERE/"prompts"
    dest.mkdir(exist_ok=True)
    for rid,row in rows.items():
        for arm in ARMS:
            (dest/f"{rid}.{arm}.txt").write_text(render(row,arm))
    order = schedule(rows)
    for job in order:
        job["request_sha256"] = hash_request(payload_for(job["record"],job["arm"],rows))
    save(HERE/"order.json",order)
    include = [p for folder in (ROOT/"circuits",HERE) for p in folder.rglob("*")
               if p.is_file() and "__pycache__" not in p.parts and not p.name.startswith(".")]
    save(path,dict(at=now(),seed=SEED,model=MODEL,ollama=SERVER,
                   socket_timeout_seconds=TIMEOUT_SECONDS,max_requests=72,sessions=72,direct_paid_api_cap_usd=0,
                   sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(include)}))
    print("Frozen",len(order),"request hashes.")


def collect():
    verify_frozen()
    verify_model()
    rows = load(RECORDS)
    order = load(HERE/"order.json")
    out = HERE/"observed"
    out.mkdir(exist_ok=True)
    with (out/"run.lock").open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for i,job in enumerate(order):
            rid,arm = job["record"],job["arm"]
            payload = payload_for(rid,arm,rows)
            receipt = stage(out/f"{rid}_{arm}"/"response.json",payload,rows[rid],job["request_sha256"])
            print(f"{i+1}/{len(order)} {rid} {arm} {receipt['status']}",flush=True)
    verify_frozen()
    verify_model()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    actions = {"freeze":freeze,"verify":verify_frozen,"preflight":verify_model,"collect":collect}
    parser.add_argument("action",choices=actions)
    actions[parser.parse_args().action]()
