"""Render, freeze, and administer the matched forced-reading experiment."""
import argparse
import fcntl
import json
import random

from instrument import HERE, ROOT, MODELS, digest, local, now, save, stage

SEED = 2026112443
ARMS = ("full", "filtered")
RECORDS = ROOT / "circuits" / "records.json"


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
        "ID stu target_current initial " + " ".join(meters) + " target_current_above_threshold",
    ]
    for sid in row["state_order"]:
        if arm == "filtered" and sid not in row["survivors"]:
            continue
        state = row["states"][sid]
        lines.append(" ".join([sid,state["bits"],state["target_current"],state["initial"],
                               *(state["obs"][m] for m in meters),"Y" if state["answer"] else "N"]))
    lines.extend(["",f"Observed readings: initial = {row['initial_reading']}; {row['meter']} = {row['reading']}.",
        "The table includes every setting compatible with both readings. Use both readings when identifying which settings remain possible.",
        "Y means the named claim holds in every compatible setting. N means it fails in every compatible setting. U means both answers are possible.",
        "For Y or N, list all and only the compatible IDs. For U, list exactly two compatible IDs with opposite target answers. Use no duplicate IDs.",
        "Both readings have already been supplied. Return only the JSON fields verdict and certificate."])
    return "\n".join(lines)


def schedule(rows):
    rng = random.Random(SEED)
    families = sorted({r['family'] for r in rows.values()})
    rng.shuffle(families)
    waves = [[], []]
    for i,family in enumerate(families):
        triplet = [(rid,r) for rid,r in rows.items() if r["family"]==family]
        for rid,row in triplet:
            is_low_decisive = row["kind"]=="decisive" and row["reading"]=="L"
            first_full = (i % 2 == 0) != is_low_decisive
            for wave,arm in zip(waves, ARMS if first_full else reversed(ARMS)):
                wave.append(dict(record=rid,arm=arm))
    for wave in waves:
        rng.shuffle(wave)
    return waves[0]+waves[1]


def verify_model():
    if local("/api/version")["version"] != "0.40.18":
        raise ValueError("Local server differs from the registered version")
    model=MODELS["gptoss"]
    if not any(m["name"]==model["tag"] and m["digest"]==model["digest"] for m in local("/api/tags")["models"]):
        raise ValueError("The registered local model is unavailable")


def verify_frozen():
    registry=json.loads((HERE/"freeze.json").read_bytes())
    for name,value in registry["sha256"].items():
        if digest(ROOT/name)!=value:
            raise ValueError(f"Frozen artifact changed: {name}")


def freeze():
    path=HERE/"freeze.json"
    if path.exists() or (HERE/"observed").exists():
        raise ValueError("Study already frozen or dispatched")
    rows=json.loads(RECORDS.read_bytes())
    families={r["family"] for r in rows.values()}
    if len(rows)!=18 or len(families)!=6:
        raise ValueError("Incomplete study panel")
    verify_model()
    dest=HERE/"prompts";dest.mkdir(exist_ok=True)
    for family in families:
        variants=[r for r in rows.values() if r["family"]==family]
        if sorted(r["kind"] for r in variants)!=["ambiguous","decisive","decisive"]:
            raise ValueError("Expected two decisive replies and one ambiguous control")
        decisive=[r for r in variants if r["kind"]=="decisive"]
        if {r["reading"] for r in decisive}!={"H","L"} or len({(r["meter"],r["initial_reading"]) for r in decisive})!=1:
            raise ValueError("Decisive twins must have opposite replies on the same meter")
    for rid,row in rows.items():
        valid={k for k,v in row["states"].items() if v["initial"]==row["initial_reading"] and v["obs"][row["meter"]]==row["reading"]}
        if len(valid)!=2 or valid!=set(row["survivors"]) or len(row["states"])!=8:
            raise ValueError(f"Invalid row intersection in {rid}")
        for arm in ARMS:
            (dest/f"{rid}.{arm}.txt").write_text(render(row,arm))
    save(HERE/"order.json",schedule(rows))
    include=[p for folder in (ROOT/"circuits",HERE) for p in folder.rglob("*") if p.is_file() and "__pycache__" not in p.parts and not p.name.startswith(".")]
    save(path,dict(at=now(),seed=SEED,model=MODELS["gptoss"],ollama="0.40.18",max_requests=36,sessions=36,
                   direct_api_spend_cap_usd=0,sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(include)}))


def administer():
    verify_frozen()
    verify_model()
    rows=json.loads(RECORDS.read_bytes())
    schedule_rows=json.loads((HERE/"order.json").read_bytes())
    indices={rid:i for i,rid in enumerate(sorted(rows))}
    out=HERE/"observed";out.mkdir(exist_ok=True)
    with (out/"run.lock").open("w") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for i,job in enumerate(schedule_rows):
            rid,arm=job["record"],job["arm"]
            messages=[dict(role="system",content=(HERE/"method.txt").read_text().strip()),
                      dict(role="user",content=(HERE/"prompts"/f"{rid}.{arm}.txt").read_text())]
            stage(out/f"{rid}_{arm}"/"response.json",messages,rows[rid],"gptoss",SEED+indices[rid],False)
            print(f"{i+1}/{len(schedule_rows)} sessions complete",flush=True)
    verify_frozen()
    verify_model()


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action",choices=("verify","freeze","run"))
    args=parser.parse_args()
    {"freeze":freeze,"verify":verify_frozen,"run":administer}[args.action]()
