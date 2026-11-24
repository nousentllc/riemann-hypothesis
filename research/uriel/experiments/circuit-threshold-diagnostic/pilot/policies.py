"""Blind, deterministic position and balance shortcuts on actionable records."""
import json
from collections import Counter
from instrument import HERE, oracle, save
from run import RECORDS

def main():
    rows=json.loads(RECORDS.read_text()); report={}
    for rid,row in rows.items():
        truth=oracle(row)
        if truth['kind']!='lookup': continue
        ids=row['eligible']; menu=list(row['menu'])
        counts=[Counter(row['states'][i]['obs'][m] for i in ids) for m in menu]
        balance=[min(c.values()) if len(c)>1 else 0 for c in counts]
        signs={k:row['states'][k]['answer'] for k in ids}
        crossing=[sum(1 for a in ids for b in ids if signs[a] and not signs[b] and row['states'][a]['obs'][m]==row['states'][b]['obs'][m]) for m in menu]
        if crossing.count(0)!=1 or menu[crossing.index(0)]!=truth['guaranteed'][0]:
            raise ValueError('Independent crossing-pair rule disagrees')
        report[rid]=dict(menu=menu,accessible_split_sizes=[dict(c) for c in counts],balance=balance,
                crossing_pairs=crossing,decisive=truth['guaranteed'][0],first_max_balance=menu[balance.index(max(balance))])
    limits={f'position_{i+1}':sum(v['menu'][i]==v['decisive'] for v in report.values()) for i in range(3)}
    limits['first_max_balance']=sum(v['first_max_balance']==v['decisive'] for v in report.values())
    result=dict(quota=len(report),solved=limits,records=report)
    save(HERE/'policy_controls.json',result)
    print(json.dumps(limits))

if __name__=='__main__':
    main()
