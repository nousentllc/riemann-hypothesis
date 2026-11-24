"""Unit-level and record-level evaluation with certificates independent of the claim sign."""
import csv
import json
from collections import Counter
from fractions import Fraction

from exact import paired
from instrument import HERE, save
from run import ARMS, RECORDS, verify_frozen


def evaluate(row, receipt):
    survivors={s for s,v in row["states"].items() if v["initial"]==row["initial_reading"] and v["obs"][row["meter"]]==row["reading"]}
    signs={Fraction(row["states"][s]["target_current"]) > Fraction(row["target_threshold"]) for s in survivors}
    expected="U" if len(signs)==2 else "Y" if True in signs else "N"
    answer=receipt.get("answer") if receipt.get("status")=="ok" else None
    answer=answer or {}
    verdict=answer.get("verdict")
    cert=answer.get("certificate",[])
    submitted=set(cert)
    duplicate=len(submitted)!=len(cert)
    ids=bool(cert) and not duplicate and submitted==survivors
    sign=expected==verdict
    barrier=("missing" if not verdict else "pass" if sign and ids else "verdict and IDs" if not(sign or ids) else "IDs" if sign else "verdict")
    return dict(expected=expected,verdict=verdict,certificate=" ".join(cert),required_ids=" ".join(sorted(survivors)),
                sign=sign,ids=ids,certified=ids and sign,unsupported=verdict in ("Y","N") and not sign,
                extra=" ".join(sorted(submitted-survivors)),omitted=" ".join(sorted(survivors-submitted)),duplicate=duplicate,
                status=receipt["status"],barrier=barrier)


def contrast(outcomes):
    c=Counter((x['full'],x['filtered']) for x in outcomes)
    w,l=c[False,True],c[True,False]
    return dict(n=len(outcomes),both=c[True,True],neither=c[False,False],full_only=l,filtered_only=w,net=w-l,**paired(w,l))


def main():
    verify_frozen()
    rows=json.loads(RECORDS.read_bytes())
    cases=[]; totals={a:Counter() for a in ARMS}
    for rid,row in sorted(rows.items()):
        for arm in ARMS:
            receipt=json.loads((HERE/"observed"/f"{rid}_{arm}"/"response.json").read_bytes())
            r=dict(record=rid,family=row["family"],kind=row["kind"],arm=arm,**evaluate(row,receipt))
            cases.append(r);t=totals[arm]; usage=receipt.get("usage",{})
            t.update(dict(sessions=1,parseable=int(r["verdict"] is not None),invalid=int(receipt["status"]!="ok"),
                length_limited=int(usage.get("done_reason")=="length"),prompt_tokens=usage.get("prompt_eval_count") or 0,
                generated_tokens=usage.get("eval_count") or 0,service_ns=usage.get("total_duration") or 0,
                unnecessary_abstention=int(r["expected"]!="U" and r["verdict"]=="U")))
            for m in ("ids","sign","certified","unsupported"):
                t[m]+=int(r[m]);t[m+"_"+r["kind"]]+=int(r[m])
    family_rows=[]
    for f in sorted({r["family"] for r in rows.values()}):
        record=dict(family=f)
        for a in ARMS:
            twins=[r for r in cases if r["arm"]==a and r["family"]==f and r["kind"]=="decisive"]
            if len(twins)!=2:raise ValueError("Incomplete twins")
            record[a]=all(r["certified"] for r in twins)
            totals[a]["complete_decisive_families"]+=int(record[a])
            totals[a]["opposite_decisive_verdicts"]+=int({r["verdict"] for r in twins}=={"Y","N"})
            totals[a]["both_decisive_signs_warranted"]+=int(all(r["sign"] for r in twins))
        family_rows.append(record)
    primary=contrast(family_rows)
    gate=(primary["net"]>=2 and totals["filtered"]["ids_decisive"]-totals["full"]["ids_decisive"]>=2 and
          totals["filtered"]["certified_ambiguous"]>=totals["full"]["certified_ambiguous"])
    summary=dict(totals=totals,primary=primary,families=family_rows,development_signal=gate,paid_api_usd=0)
    folder=HERE/"results";save(folder/"summary.json",summary)
    with (folder/"cases.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=list(cases[0]));w.writeheader();w.writerows(cases)
    print(json.dumps(summary,indent=2))

if __name__=="__main__":
    main()
