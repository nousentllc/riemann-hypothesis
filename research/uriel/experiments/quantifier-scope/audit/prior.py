"""Recover the historical seven from the pinned parent receipts (optional cross-study replay)."""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

COMMIT = "e7a01b2d19e61e77b97ece9f1b48d48bb761e186"
BASE = f"https://github.com/nousentllc/riemann-hypothesis/blob/{COMMIT}/research/uriel/experiments/label-first-verdict/"
HERE = Path(__file__).resolve().parent


def recover(root):
    rows = json.loads((root / "circuits/records.json").read_bytes())
    cases = {}
    accurate_delivered = 0
    cells = Counter()
    for record, row in sorted(rows.items()):
        observed = Path("pilot/observed") / (record + "_label_first")
        labpath = observed / "labels/response.json"
        finalpath = observed / "verdict/response.json"
        if not (root / finalpath).exists():
            continue
        raw = [(root / p).read_bytes() for p in (labpath, finalpath)]
        lab, final = (json.loads(x) for x in raw)
        if any(receipt["status"] != "ok" for receipt in (lab, final)):
            continue
        surviving = [sid for sid in row["state_order"] if row["states"][sid]["initial"] == row["initial_reading"]
                     and row["states"][sid]["obs"][row["meter"]] == row["reading"]]
        truth = {sid: "Y" if Fraction(row["states"][sid]["target_current"]) > Fraction(row["target_threshold"]) else "N"
                 for sid in surviving}
        public_lab, public_final = (json.loads(receipt["content"]) for receipt in (lab, final))
        if truth != public_lab:
            continue
        accurate_delivered += 1
        warranted = next(iter(truth.values())) if len(set(truth.values())) == 1 else "U"
        cells[warranted,public_final["verdict"]] += 1
        if public_final["verdict"] == warranted:
            continue
        assert warranted == "U" and public_final["verdict"] == "Y"
        ids = public_final["certificate"]
        evidence = "both" if set(ids) == set(truth) and len(ids) == 2 else "positive_only" if len(ids) == 1 and truth.get(ids[0]) == "Y" else "other"
        cases[record] = dict(family=row["family"], ordered_ids=surviving, truth=truth, warranted=warranted,
                             checkpoint_text=lab["content"], final_text=final["content"], evidence=evidence,
                             checkpoint_source=BASE + str(labpath), final_source=BASE + str(finalpath),
                             checkpoint_sha256=sha256(raw[0]).hexdigest(), final_sha256=sha256(raw[1]).hexdigest())
    assert cells == {('U','Y'):7,('U','U'):1,('Y','Y'):6,('N','N'):4}
    assert accurate_delivered == 18 and len(cases) == 7
    assert sum(c["evidence"]=="both" for c in cases.values())==2
    assert sum(c["evidence"]=="positive_only" for c in cases.values())==5
    return dict(commit=COMMIT, previous_contract="Three-way consensus (Y, N, U) and witness IDs",
                records=24, delivered_after_accurate_checkpoint=accurate_delivered,
                physically_mixed_with_accurate_checkpoint_and_delivered_final=sum(n for (s,_),n in cells.items() if s=="U"),
                conditional_cells=[dict(warranted=w,delivered=d,records=cells[w,d]) for w,d in sorted(cells)], cases=cases)


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("parent_study",type=Path)
    p.add_argument("--write",action="store_true")
    args=p.parse_args()
    text=json.dumps(recover(args.parent_study),indent=2)+"\n"
    dest=HERE/"historical_seven.json"
    if args.write:dest.write_text(text)
    else:assert dest.read_text()==text
    print("Verified the seven historical mixed-to-yes judgments from visible source responses.")
