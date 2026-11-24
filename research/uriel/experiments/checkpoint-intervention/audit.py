"""Independent, offline request and score replay. Optional prior-Git source verification."""
import argparse
import csv
from collections import Counter
from datetime import datetime
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parent
REGISTERED=datetime.fromisoformat('2026-11-24T18:30:26-05:00')


def get(path):
    return json.loads((ROOT/path).read_bytes())


def blobcheck(repo):
    s=get('sources.json')
    def read(path):
        raw=subprocess.check_output(['git','-C',repo,'cat-file','blob',s['parent']+':'+s['prefix']+path])
        assert hashlib.sha256(raw).hexdigest()==s['sha256'][path]
        return json.loads(raw)
    p=get('panel.json'); records=read('circuits/records.json')
    selected={r for r,v in records.items() if len({v['states'][i]['answer'] for i in v['survivors']})==1}
    assert selected==set(p)
    for rid,row in p.items():
        source=records[rid];ids=source['survivors']
        assert (ids,[source['states'][i]['target_current'] for i in ids],source['target_threshold'])==(row['ids'],row['currents'],row['threshold'])
        d='pilot/observed/'+rid+'/'
        assert read(d+'labels/response.json')['content']==row['old_label']
        for q in ('any','both'):
            assert read(d+q+'/request.json')==row['requests'][q]
            assert read(d+q+'/response.json')['answer']['answer']==row['old_answers'][q]


def evaluate():
    pnl=get('panel.json'); ordered=get('freeze.json')['schedule']
    rows={};old=REGISTERED; first=Counter();attention=[]
    for ix,job in enumerate(ordered):
        rid,q,arm=[job[k] for k in ('record','question','arm')]
        row=pnl[rid]; base=row['requests'][q]
        path=Path('observed')/rid/q/arm
        msg=get(path/'request.json');r=get(path/'response.json');j=get(path/'response.started')
        assert datetime.fromisoformat(r['started'])>=old
        old=datetime.fromisoformat(r['ended']); assert old>=datetime.fromisoformat(r['started'])
        assert j=={k:r[k] for k in ('request_sha256','started')}
        assert hashlib.sha256(json.dumps(msg,sort_keys=True).encode()).hexdigest()==job['sha256']==r['request_sha256']
        h=msg['messages'][2];old_text=base['messages'][2]['content']
        txt=h['content']; delta=[(x,y) for x,y in zip(txt,old_text) if x!=y]
        assert len(txt)==len(old_text) and all({x,y}=={'N','Y'} for x,y in delta)
        assert len(delta)==(0 if job['prior_replay'] else 1)
        assert h['role']=='assistant'
        msg['messages'][2]['content']=old_text
        assert msg==base
        labels=json.loads(txt); pp=row['truth'][0]; assert set(labels)==set(row['ids'])
        assert all(s in ('N','Y') for s in labels.values())
        assert sum(s!=pp for s in labels.values())==(arm=='conflict')
        if arm=='conflict': assert labels[job['target']]!=pp
        replay=str(job['prior_replay'])
        if r['status']=='ok':
            parsed=json.loads(r['content'])
            assert set(parsed)=={'answer'} and parsed['answer'] in ('Y','N') and parsed==r['answer'] and r['usage']['done_reason']=='stop'
            value=parsed['answer']
        else:
            assert r['answer'] is None;value='?'
        pred='Y' if (any if q=='any' else all)(s=='Y' for s in labels.values()) else 'N'
        key=(rid,q); record=rows.setdefault(key,{})
        assert arm not in record;record[arm]=(pred,value,replay)
        if ix%2==0:
            assert (ordered[ix+1]['record'],ordered[ix+1]['question'])==key
            first[row['truth'],q,arm]+=1
    assert len(rows)==24 and len(first)==8 and set(first.values())=={3}
    with (ROOT/'cases.csv').open() as stream: cases=list(csv.DictReader(stream))
    assert len(cases)==len(rows) and set(rows)=={(x['record'],x['question']) for x in cases}
    groups={k:Counter() for k in ('five_original_errors','affected','invariant')};replay_hits=usable=0
    for c in cases:
        rid,q=c['record'],c['question']; a,b=(rows[rid,q][key] for key in ('faithful','conflict'))
        expected=(a[0],b[0]);actual=(a[1],b[1])
        assert expected==(c['predicted_faithful'],c['predicted_conflict'])
        assert actual==(c['faithful'],c['conflict']) and str(actual==expected)==c['report_rule_pair']
        assert (a[2]=='True')!=(b[2]=='True')
        historic=pnl[rid]['old_answers'][q]
        replay_hits+=historic==(a[1] if a[2]=='True' else b[1])
        usable+=sum(v!='?' for v in actual)
        affected=a[0]!=b[0]; cohorts=['affected' if affected else 'invariant']
        if affected and b[2]=='True':cohorts.append('five_original_errors')
        for group in cohorts:
            tally=groups[group];tally['n']+=1;tally['match']+=actual==expected;tally[''.join(actual)]+=1
        if actual!=expected:attention.append([rid,q,*actual,*expected])
    summary=get('results.json')
    for group,counts in groups.items():
        assert counts.pop('n')==summary[group]['n']
        assert counts.pop('match',0)==summary[group]['paired_report_prediction']
        assert dict(counts)==summary[group]['patterns']
    assert usable==summary['usable'] and replay_hits==summary['replays']
    assert len(list((ROOT/'observed').rglob('response.json')))==len(ordered)==48
    return dict(calls=48,records=12,usable=usable,historical_replay_hits=replay_hits,
                pending_or_discrepant_with_checkpoint=attention)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path);p.add_argument('--write',action='store_true')
    a=p.parse_args()
    if a.repo:blobcheck(a.repo)
    result=evaluate()
    data=json.dumps(result,indent=2)+'\n'
    if a.write:(ROOT/'audit.json').write_text(data)
    else:assert (ROOT/'audit.json').read_text()==data
    print(data)
