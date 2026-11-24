"""Test prompt surface, survivor markings, follow-up balance, and absence of grammar leaks."""
from collections import Counter, defaultdict
from itertools import permutations

from instrument import request_payload
from run import ARMS, RECORDS, check_panel, load, render, schedule


def check():
    rows = load(RECORDS)
    check_panel(rows)
    for rid,row in rows.items():
        unmarked,marked,filtered = [render(row,a).splitlines() for a in ARMS]
        full_rows = [s for s in unmarked if s.startswith(". ")]
        good_ids = set(row["survivors"])
        if len(full_rows) != 8:
            raise ValueError(rid)
        expected_m = ["*"+s[1:] if s in full_rows and s.split()[1] in good_ids else s for s in unmarked]
        expected_f = [s for s in unmarked if s not in full_rows or s.split()[1] in good_ids]
        if expected_m != marked or expected_f != filtered:
            raise ValueError("Surface mismatch "+rid)
        if len([s for s in marked if s.startswith("* ")]) != 2:
            raise ValueError("Incorrect number of marks")
        enum = request_payload([],row,0)["format"]["properties"]["certificate"]["items"]["enum"]
        if set(enum) != set(row["states"]):
            raise ValueError("Schema narrowed eligible IDs")
    jobs = schedule(rows)
    if len(jobs) != 72 or len({(j["record"],j["arm"]) for j in jobs}) != 72:
        raise ValueError("Incorrect sessions")
    orders = defaultdict(list)
    for job in jobs:
        orders[job["record"]].append(job["arm"])
    for kind in ("decisive","ambiguous"):
        for reading in ("H","L"):
            observed = Counter(tuple(orders[rid]) for rid,row in rows.items() if (row["kind"],row["reading"])==(kind,reading))
            if observed != Counter(permutations(ARMS)):
                raise ValueError("Imbalanced arm orders")
    for start in (0,24,48):
        wave = jobs[start:start+24]
        if len({j["record"] for j in wave}) != 24 or Counter(j["arm"] for j in wave) != dict.fromkeys(ARMS,8):
            raise ValueError("Wave imbalance")
    print("Verified 24 display triples, all eight allowed IDs, 72 distinct sessions, and six arm orders per record type.")


if __name__ == "__main__":
    check()
