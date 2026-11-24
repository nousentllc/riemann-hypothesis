"""One-character checkpoint intervention on the two homogeneous records per layout."""
import argparse
from collections import Counter
from copy import deepcopy
import csv
import fcntl
from fractions import Fraction
import json
from pathlib import Path
import random
import re

from instrument import digest, hash_request, save, stage, verify_model

ROOT = Path(__file__).resolve().parent
PANEL = json.loads((ROOT/'panel.json').read_text())
FILES = ('panel.json','sources.json','instrument.py','study.py','PROTOCOL.md')
SEED = 2026112421
QUESTIONS = ('any','both')
MAPS = ('faithful','conflict')


def make_requests():
    jobs = []
    for rid, row in sorted(PANEL.items()):
        truth = row['truth']
        assert truth in ('NN','YY')
        public = dict(zip(row['ids'],truth))
        for sid,current in zip(row['ids'],row['currents']):
            assert public[sid] == ('Y' if Fraction(current)>Fraction(row['threshold']) else 'N')
        prior = json.loads(row['old_label'])
        changed = [sid for sid in row['ids'] if prior[sid]!=public[sid]]
        k = int(row['family'].removeprefix('DC-K'))
        if changed:
            target, = changed
        else:
            target = row['ids'][1 if truth=='NN' else (k-1)%2]
        for q in QUESTIONS:
            base=row['requests'][q]
            assert base['messages'][2]['content']==row['old_label']
            assert base['messages'][2]['role']=='assistant'
            mask=r'("' + re.escape(target) + r'"\s*:\s*")([YN])(")'
            for arm in MAPS:
                bit=public[target] if arm=='faithful' else ('N' if public[target]=='Y' else 'Y')
                checkpoint,n=re.subn(mask,lambda m:m[1]+bit+m[3],row['old_label'])
                assert n == 1 and json.loads(checkpoint) == dict(public, **{target:bit})
                request=deepcopy(base)
                request['messages'][2]['content']=checkpoint
                jobs.append((dict(record=rid,question=q,arm=arm,target=target,family=row['family'],
                                  prior_replay=(checkpoint==row['old_label']),sha256=hash_request(request)),request))
    assert len(jobs)==48 and sum(j['prior_replay'] for j,_ in jobs)==24
    # Randomize pair order; assign opposite within-pair dispatch orders equally in each stratum.
    rng=random.Random(SEED)
    pairs={}
    for j,r in jobs:
        pairs.setdefault((j['record'],j['question']),[]).append((j,r))
    for truth in ('NN','YY'):
        for q in QUESTIONS:
            keys=sorted(key for key in pairs if PANEL[key[0]]['truth']==truth and key[1]==q)
            assert len(keys)==6
            for key in rng.sample(keys,3):
                pairs[key].reverse()
    keys=sorted(pairs)
    rng.shuffle(keys)
    return [job for key in keys for job in pairs[key]]


def manifest():
    return dict(files={f:digest(ROOT/f) for f in FILES},schedule=[j for j,_ in make_requests()])


def verify():
    assert json.loads((ROOT/'freeze.json').read_text())==manifest()


def collect():
    verify()
    verify_model()
    with (ROOT/'run.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for n,(job,payload) in enumerate(make_requests(),1):
            rid,q,arm=[job[k] for k in ('record','question','arm')]
            path=ROOT/'observed'/rid/q/arm/'response.json'
            r=stage(path,payload,PANEL[rid],job['sha256'],q)
            print(n,rid,q,arm,r['status'],flush=True)
    verify_model()


def score():
    verify()
    answers={}
    for job,payload in make_requests():
        rid,q,arm=[job[k] for k in ('record','question','arm')]
        folder=ROOT/'observed'/rid/q/arm
        receipt=json.loads((folder/'response.json').read_text())
        assert json.loads((folder/'request.json').read_text())==payload
        assert receipt['request_sha256']==job['sha256']
        out=receipt['answer']['answer'] if receipt['status']=='ok' else '?'
        answers[rid,q,arm]=(out,job)
    cases=[]
    for rid,row in sorted(PANEL.items()):
        truth=row['truth'][0]
        for q in QUESTIONS:
            affected=(q=='any')==(truth=='N')
            a,ja=answers[rid,q,'faithful']; b,jb=answers[rid,q,'conflict']
            expected_conflict=('Y' if truth=='N' else 'N') if affected else truth
            reanswer=a if ja['prior_replay'] else b
            cases.append(dict(record=rid,family=row['family'],physical=row['truth'],question=q,
                affected=affected,edited_id=ja['target'],faithful=a,conflict=b,
                predicted_faithful=truth,predicted_conflict=expected_conflict,
                orientation=a+b,report_rule_pair=(a,b)==(truth,expected_conflict),
                prior_arm='faithful' if ja['prior_replay'] else 'conflict',
                prior_answer=row['old_answers'][q],replay_answer=reanswer))
    result={}
    for name,group in [('five_original_errors',[c for c in cases if c['affected'] and c['prior_arm']=='conflict']),
                       ('affected',[c for c in cases if c['affected']]),('invariant',[c for c in cases if not c['affected']])]:
        result[name]=dict(n=len(group),paired_report_prediction=sum(c['report_rule_pair'] for c in group),
                          patterns=dict(Counter(c['orientation'] for c in group)))
    result['replays']=sum(c['prior_answer']==c['replay_answer'] for c in cases)
    result['usable']=sum(v[0]!='?' for v in answers.values())
    with (ROOT/'cases.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=cases[0]);w.writeheader();w.writerows(cases)
    save(ROOT/'results.json',result)
    print(json.dumps(result))


if __name__=='__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('action',choices=('freeze','verify','collect','score'))
    action=cli.parse_args().action
    if action=='freeze':
        assert not (ROOT/'freeze.json').exists() and not (ROOT/'observed').exists()
        save(ROOT/'freeze.json',manifest())
    else:
        {'verify':verify,'collect':collect,'score':score}[action]()
