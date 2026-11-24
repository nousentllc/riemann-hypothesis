"""Score all 72 sessions and compare complete paired layouts."""
import csv
from collections import Counter
from fractions import Fraction
import json

from exact import paired
from instrument import HERE, save
from run import ARMS, RECORDS, load, survivors, verify_frozen

COMPARISONS = (("marked","filtered"),("marked","unmarked"),("filtered","unmarked"))


def implication(signs):
    return "Y" if signs == {True} else "N" if signs == {False} else "U" if len(signs) == 2 else None


def evaluate(row, receipt):
    kept = survivors(row)
    labels = {sid:Fraction(s["target_current"]) > Fraction(row["target_threshold"]) for sid,s in row["states"].items()}
    expected = implication({labels[s] for s in kept})
    answer = (receipt.get("answer") if receipt.get("status") == "ok" else None) or {}
    verdict = answer.get("verdict")
    cert = answer.get("certificate",[])
    submitted = set(cert)
    duplicate = len(cert) != len(submitted)
    ids = submitted == kept and not duplicate
    sign = verdict == expected
    own = implication({labels[s] for s in submitted})
    return dict(expected=expected,verdict=verdict,certificate=" ".join(cert),required_ids=" ".join(sorted(kept)),
                sign=sign,ids=ids,certified=ids and sign,submitted_implies=own,coherent=verdict is not None and verdict == own,
                two_distinct=len(cert) == len(submitted) == 2,
                unsupported=verdict in ("Y","N") and verdict != expected,
                extra=" ".join(sorted(submitted-kept)),omitted=" ".join(sorted(kept-submitted)),
                duplicate=duplicate,status=receipt["status"])


def contrast(primary, reference, left, right):
    matched = Counter((x[left],x[right]) for x in primary)
    wins,losses = matched[True,False],matched[False,True]
    return dict(n=len(primary),both=matched[True,True],neither=matched[False,False],
                left_only=wins,right_only=losses,net=wins-losses,net_fraction=(wins-losses)/len(primary),
                left_only_ids=[r[reference] for r in primary if r[left] and not r[right]],
                right_only_ids=[r[reference] for r in primary if r[right] and not r[left]])


def main():
    verify_frozen()
    rows = load(RECORDS)
    cases = []
    totals = {a:Counter() for a in ARMS}
    for rid,row in sorted(rows.items()):
        for arm in ARMS:
            receipt = load(HERE/"observed"/f"{rid}_{arm}"/"response.json")
            case = dict(record=rid,family=row["family"],kind=row["kind"],meter=row["meter"],
                        reading=row["reading"],arm=arm,**evaluate(row,receipt))
            cases.append(case)
            tally = totals[arm]
            usage = receipt.get("usage",{})
            tally.update(dict(sessions=1,parseable=int(receipt["status"]=="ok"),
                              service_observed=int(isinstance(usage.get("total_duration"),int)),
                              length_limited=int(usage.get("done_reason")=="length"),
                              prompt_tokens=usage.get("prompt_eval_count") or 0,generated_tokens=usage.get("eval_count") or 0,
                              service_ns=usage.get("total_duration") or 0))
            for metric in ("sign","ids","certified","unsupported","two_distinct","coherent","duplicate"):
                tally[metric] += int(case[metric])
                tally[metric+"_"+case["kind"]] += int(case[metric])
            tally["two_distinct_coherent"] += int(case["two_distinct"] and case["coherent"])
            tally["two_distinct_inadmissible"] += int(case["two_distinct"] and not case["ids"])
            tally["unwarranted_abstention"] += int(case["expected"] != "U" and case["verdict"] == "U")
    families = []
    for family in sorted({r["family"] for r in rows.values()}):
        family_result = dict(family=family)
        for arm in ARMS:
            subset = [r for r in cases if (r["family"],r["arm"]) == (family,arm)]
            decisive = [r for r in subset if r["kind"] == "decisive"]
            ambiguous = [r for r in subset if r["kind"] == "ambiguous"]
            if len(decisive) != 2 or len(ambiguous) != 2:
                raise ValueError(f"Incomplete family {family}")
            result = dict(complete_decisive=all(r["certified"] for r in decisive),
                          possible_decisive=all(r["certified"] or r["status"]!="ok" for r in decisive),
                          complete_ambiguous=all(r["certified"] for r in ambiguous),
                          complete_quartet=all(r["certified"] for r in subset),
                          both_decisive_signs=all(r["sign"] for r in decisive),
                          both_ambiguous_signs=all(r["sign"] for r in ambiguous))
            family_result[arm] = result
            for key,value in result.items():
                totals[arm][key] += int(value)
        families.append(family_result)
    comparisons = {}
    for left,right in COMPARISONS:
        c = {}
        for metric in ("complete_decisive","complete_ambiguous","complete_quartet"):
            framed = [dict(family=r["family"],**{a:r[a][metric] for a in ARMS}) for r in families]
            c[metric] = contrast(framed,"family",left,right)
        primary = c["complete_decisive"]
        primary.update(paired(primary["left_only"],primary["right_only"]))
        primary["missing_completion_net_bounds"] = [totals[left]["complete_decisive"] - totals[right]["possible_decisive"],
                                                    totals[left]["possible_decisive"] - totals[right]["complete_decisive"]]
        records = [dict(record=rid,**{r["arm"]:r["certified"] for r in cases if r["record"]==rid}) for rid in rows]
        c["cases"] = contrast(records,"record",left,right)
        comparisons[left+"_vs_"+right] = c
    summary = dict(arms=list(ARMS),totals=totals,families=families,comparisons=comparisons,paid_api_usd=0)
    folder = HERE/"results"
    save(folder/"summary.json",summary)
    with (folder/"cases.csv").open("w",newline="") as stream:
        writer = csv.DictWriter(stream,fieldnames=list(cases[0]))
        writer.writeheader()
        writer.writerows(cases)
    print(json.dumps({a:{k:v for k,v in t.items() if k in ("sessions","complete_decisive","complete_ambiguous","complete_quartet","certified")} for a,t in totals.items()}))


if __name__ == "__main__":
    main()
