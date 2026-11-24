"""Regression controls for a sequential experiment. All fabricated transcripts stay in temporary storage."""
from contextlib import redirect_stdout
from datetime import datetime, timedelta, timezone
from io import StringIO
import json
from pathlib import Path
import shutil
import sys
from tempfile import TemporaryDirectory

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'pilot'))
from instrument import hash_request,request_payload
from run import initial,followup,read
from check import audit
import check
import analyze
import run

def write(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj)+'\n')

def test():
    rows=read(run.ROWS)
    order=read(run.HERE/'order.json')
    clock=datetime(2027,1,1,tzinfo=timezone.utc)
    def fake(directory,ask,answer):
        nonlocal clock
        start=clock; clock+=timedelta(seconds=1)
        visible='' if answer is None else json.dumps(answer,indent=1)
        write(directory/'request.json',ask)
        write(directory/'response.json',dict(request_sha256=hash_request(ask),content=visible,answer=answer,
              status='invalid' if answer is None else 'ok',usage={'done_reason':'length' if answer is None else 'stop'},
              started=start.isoformat(),ended=clock.isoformat()))
        return visible
    with TemporaryDirectory() as tmp:
        home=Path(tmp); pp=home/'pilot'; (home/'audit').mkdir(); pp.mkdir()
        reg=read(ROOT/'pilot/freeze.json')
        for name in [*reg['sha256'],'pilot/freeze.json']:
            p=home/name;p.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(ROOT/name,p)
        direct_errors=0
        for j in order:
            rid,arm=j['record'],j['arm'];row=rows[rid];i=int(rid.split('-')[1]);seed=2026112467+i
            modes='direct' if arm=='direct' else 'labels'
            base=initial(rid,row,modes); path=pp/'observed'/f'{rid}_{arm}'
            ids=row['survivors'];labs={s:'Y' if row['states'][s]['answer'] else 'N' for s in ids}
            target='U' if len(set(labs.values()))==2 else next(iter(labs.values()))
            alternate='U' if target!='U' else 'N'
            final={'verdict':target,'certificate':ids[::-1]}
            if arm=='direct':
                if i%4==0:final['verdict']=alternate;direct_errors+=1
                fake(path/'direct',request_payload(base,row,seed,'direct'),final);continue
            label=None if i==0 else dict(labs)
            if label and i in (2,3):
                label[ids[0]]='N' if label[ids[0]]=='Y' else 'Y'
            raw=fake(path/'labels',request_payload(base,row,seed+1000,'labels'),label)
            if label:
                if i==4:final['verdict']=alternate
                if i==3:final['verdict']='U' if len(set(label.values()))==2 else next(iter(label.values()))
                if i==5:final['certificate']=[ids[0],ids[0]]
                fake(path/'verdict',request_payload(followup(base,raw),row,seed,'verdict'),None if i==1 else final)
        old=(run.HERE,run.ROOT,analyze.HERE,analyze.ROWS,check.P,check.ROOT)
        try:
            run.HERE=analyze.HERE=check.P=pp
            run.ROOT=check.ROOT=home
            analyze.ROWS=home/'circuits/records.json'
            with redirect_stdout(StringIO()): analyze.main()
            report=audit(); c=report['cases']
            assert report['verified_requests']==71 and report['counts']['direct']['wrong']==direct_errors
            assert c['label-00_label_first']['final_status']=='gated' and c['label-01_label_first']['final_status']=='invalid'
            assert c['label-02_label_first']['label_hits']==1 and c['label-02_label_first']['warranted']
            assert c['label-03_label_first']['label_hits']==1 and not c['label-03_label_first']['warranted']
            assert c['label-04_label_first']['label_hits']==2 and not c['label-04_label_first']['warranted']
            assert c['label-05_label_first']['warranted'] and not c['label-05_label_first']['certified']
            mutated=pp/'observed/label-02_label_first/verdict'
            req=read(mutated/'request.json')
            req['messages'][-2]['content']=req['messages'][-2]['content'].replace(' ', '  ')
            write(mutated/'request.json',req)
            receipt=read(mutated/'response.json');receipt['request_sha256']=hash_request(req)
            write(mutated/'response.json',receipt)
            try:audit()
            except ValueError as ex: assert str(ex).startswith('Unexpected payload')
            else:raise AssertionError('Reformatted checkpoint was silently passed')
        finally:
            run.HERE,run.ROOT,analyze.HERE,analyze.ROWS,check.P,check.ROOT=old
    print('Verified 48 isolated fixture workflows, gating, missing finals, mislabeled rows, contradictory verdicts, duplicate IDs and message tampering.')

if __name__=='__main__': test()
