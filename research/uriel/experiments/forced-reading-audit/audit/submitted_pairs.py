"""Classify submitted IDs by their relationship to the two observations (supplement)."""
from collections import Counter
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def examine(record, receipt):
    if receipt.get("status")!="ok":
        return {"parseable":False,"unique_pair":False,"duplicate_occurrences":0,"extra_occurrences":{}}
    answer=receipt["answer"]
    ids=answer["certificate"]
    labels={s:record["states"][s]["answer"] for s in ids}
    extra=Counter()
    for sid in ids:
        v=record["states"][sid]
        first=v["initial"]!=record["initial_reading"]
        second=v["obs"][record["meter"]]!=record["reading"]
        if first or second:
            category="both" if first and second else "initial_only" if first else "meter_only"
            extra[category]+=1
    pair=len(ids)==len(labels)==2
    data=dict(parseable=True,unique_pair=pair,duplicate_occurrences=len(ids)-len(labels),extra_occurrences=dict(extra))
    if pair:
        signs=set(labels.values())
        expected="U" if len(signs)==2 else "Y" if True in signs else "N"
        data.update(named_pair_verdict=expected,consistent_with_named_pair=expected==answer["verdict"],
                    admissible=set(ids)==set(record["survivors"]))
    return data


def main():
    rows=json.loads((ROOT/"circuits/records.json").read_bytes())
    totals={};cases={}
    for arm in ("full","filtered"):
        n=Counter();cats=Counter()
        for rid,row in sorted(rows.items()):
            receipt=json.loads((ROOT/"pilot/observed"/f"{rid}_{arm}"/"response.json").read_bytes())
            result=examine(row,receipt);cases[f"{rid}_{arm}"]=result
            n["sessions"]+=1;n["parseable"]+=result["parseable"];n["unique_pairs"]+=result["unique_pair"]
            n["duplicate_occurrences"]+=result["duplicate_occurrences"];cats.update(result["extra_occurrences"])
            if result["unique_pair"]:
                n["pair_consistent"]+=result["consistent_with_named_pair"]
                n["pair_inadmissible"]+=not result["admissible"]
                n["consistent_but_inadmissible"]+=result["consistent_with_named_pair"] and not result["admissible"]
        totals[arm]={"counts":dict(n),"extra_occurrences":dict(cats)}
    out=ROOT/"audit/submitted_pairs.json"
    out.write_text(json.dumps({"totals":totals,"cases":cases},indent=2,sort_keys=True)+"\n")
    print(json.dumps(totals,indent=2))


if __name__=="__main__":
    main()
