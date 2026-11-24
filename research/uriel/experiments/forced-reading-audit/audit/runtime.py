"""Summarize externally observed response times, separately from server-returned token and service counters."""
from datetime import datetime
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def main():
    jobs=json.loads((ROOT/'pilot/order.json').read_bytes())
    totals={a:dict(sessions=0,timestamped=0,wall_seconds=0,service_reports=0,service_seconds=0,
                   generated_token_reports=0,reported_generated_tokens=0) for a in ('full','filtered')}
    intervals=[]
    for job in jobs:
        key=f"{job['record']}_{job['arm']}"
        receipt=json.loads((ROOT/'pilot/observed'/key/'response.json').read_bytes())
        t=totals[job['arm']];t['sessions']+=1
        if 'started' in receipt and 'ended' in receipt:
            start=datetime.fromisoformat(receipt['started']);end=datetime.fromisoformat(receipt['ended'])
            t['wall_seconds']+=(end-start).total_seconds();t['timestamped']+=1
            intervals.append((start,end))
        usage=receipt.get('usage',{})
        if usage.get('total_duration') is not None:
            t['service_reports']+=1;t['service_seconds']+=usage['total_duration']/1e9
        if usage.get('eval_count') is not None:
            t['generated_token_reports']+=1;t['reported_generated_tokens']+=usage['eval_count']
    span=(max(e for _,e in intervals)-min(s for s,_ in intervals)).total_seconds() if intervals else None
    data=dict(totals=totals,timestamped_dispatch_span_seconds=span,paid_api_usd=0)
    (ROOT/'audit/runtime.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(data,indent=2))


if __name__=='__main__':
    main()
