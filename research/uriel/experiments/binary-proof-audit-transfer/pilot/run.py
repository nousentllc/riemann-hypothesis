"""Freeze, administer and resume a bounded loopback-only research pilot."""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import urllib.request
from domain import ARMS, HERE, ROOT, MODELS, SEED, build_data, digest, public_task, save, schedule

class BlockRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        raise RuntimeError('Local service redirect refused')

client=urllib.request.build_opener(urllib.request.ProxyHandler({}),BlockRedirect())
def local(path, payload=None):
    req=urllib.request.Request('http://127.0.0.1:11434'+path,
        data=json.dumps(payload).encode() if payload is not None else None,
        headers={'Content-Type':'application/json'})
    with client.open(req,timeout=300) as response: return json.load(response)

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def schema(row,choose):
    fields={'verdict':{'type':'string','enum':['Y','N','U']},
            'certificate':{'type':'array','items':{'type':'string','enum':list(row['states'])},
                'minItems':1,'maxItems':len(row['states'])}}
    if choose: fields['lookup']={'type':'string','enum':['NONE',*row['menu']]}
    return dict(type='object',properties=fields,required=list(fields),additionalProperties=False)

def frozen_paths():
    paths=[HERE/'DESIGN.md',HERE/'run.py',HERE/'domain.py',HERE/'analysis.py',
           HERE/'scorer_checks.py',*(HERE/'instructions').glob('*.txt')]
    paths.extend(ROOT / name for name in ('circuits/cases.py','circuits/design.json','circuits/network.py','formal/cases.py'))
    return sorted(set(paths))

def freeze(part,model):
    rows=build_data()[part]; jobs=schedule(rows,part)
    folder=HERE/'registry'/(part+'-'+model)
    if (folder/'FROZEN.json').exists(): raise ValueError('Registry already frozen')
    files=frozen_paths()
    save(folder/'records.json',rows); save(folder/'order.json',jobs)
    version=local('/api/version')['version']
    pins=local('/api/tags')['models']
    if not any(v['name']==MODELS[model]['tag'] and v['digest']==MODELS[model]['digest'] for v in pins):
        raise ValueError('Pinned installed model unavailable')
    if part=='test':
        decision=HERE/'development_decision.json'
        if json.loads(decision.read_text())['selected']!=model: raise ValueError('Development decision mismatch')
        files.append(decision)
    files+= [folder/'records.json',folder/'order.json']
    save(folder/'FROZEN.json',dict(at=now(),model=MODELS[model],ollama=version,seed=SEED,
                  direct_api_spend_cap_usd=0,session_count=len(jobs),max_requests=len(jobs)*2,
                  sha256={str(p.relative_to(ROOT)):digest(p) for p in files}))
    print(part,model,len(jobs),'sessions frozen with Ollama',version)

def check_manifest(part, model, check_server=True):
    folder=HERE/'registry'/(part+'-'+model)
    manifest=json.loads((folder/'FROZEN.json').read_text())
    for name,wanted in manifest['sha256'].items():
        if digest(ROOT/name)!=wanted: raise ValueError('Freeze mismatch: '+name)
    if check_server:
        if local('/api/version')['version']!=manifest['ollama']: raise ValueError('Ollama version changed')
        pins=local('/api/tags')['models']
        if not any(v['name']==manifest['model']['tag'] and v['digest']==manifest['model']['digest'] for v in pins):
            raise ValueError('Model digest changed')
    return folder,manifest

def stage(path, messages, row, model, seed, choose):
    settings=MODELS[model]
    payload=dict(model=settings['tag'],messages=messages,format=schema(row,choose),stream=False,
        keep_alive='9m',options=dict(seed=seed,temperature=0,num_ctx=8192,num_predict=settings['max_tokens']))
    if 'think' in settings: payload['think']=settings['think']
    request_hash=hashlib.sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()
    if path.exists():
        receipt=json.loads(path.read_text())
        if receipt['request_sha256']!=request_hash: raise ValueError('Existing receipt does not match')
        return receipt
    journal=path.with_suffix('.started')
    if journal.exists():
        # Unknown outcome after interruption is scored as missing rather than repeated.
        receipt=dict(request_sha256=request_hash,status='interrupted',answer=None,started=journal.read_text())
        save(path,receipt); return receipt
    path.parent.mkdir(parents=True,exist_ok=True)
    started=now()
    with journal.open('x') as f: f.write(started)
    receipt=dict(started=started,request_sha256=request_hash,answer=None)
    try:
        result=local('/api/chat',payload)
        if result['model']!=settings['tag']: raise RuntimeError('Unexpected response model')
        content=result.get('message',{}).get('content','')
        receipt.update(status='invalid',content=content,usage={k:result.get(k) for k in (
            'prompt_eval_count','eval_count','total_duration','load_duration','eval_duration','done_reason')})
        if result.get('done') and result.get('done_reason')=='stop':
            try: a=json.loads(content)
            except ValueError: a=None
            fields={'verdict','certificate','lookup'} if choose else {'verdict','certificate'}
            if (isinstance(a,dict) and set(a)==fields and a['verdict'] in ('Y','N','U')
                    and isinstance(a['certificate'],list) and all(isinstance(s,str) and s in row['states'] for s in a['certificate'])
                    and (not choose or a['lookup'] in ['NONE',*row['menu']])):
                receipt.update(status='ok',answer=a)
    except (OSError,ValueError,KeyError) as ex:
        receipt.update(status='error',error=str(ex)[:250])
    receipt['ended']=now(); save(path,receipt)
    return receipt

def administer(part,model):
    folder,manifest=check_manifest(part,model)
    rows=json.loads((folder/'records.json').read_text())
    jobs=json.loads((folder/'order.json').read_text())
    out=HERE/'observed'/(part+'-'+model)
    out.mkdir(parents=True,exist_ok=True)
    with (out/'run.lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for index,job in enumerate(jobs):
            rid,arm=job['record'],job['arm']
            row=rows[rid]
            seed=SEED+int(rid.split('-')[-1])
            messages=[dict(role='system',content=(HERE/'instructions'/(arm+'.txt')).read_text().strip()),
                      dict(role='user',content=public_task(row))]
            key=out/(rid+'_'+arm)
            first=stage(key/'first.json',messages,row,model,seed,True)
            session={'record':rid,'arm':arm,'first':first}
            selected=(first['answer'] or {}).get('lookup')
            if selected in row['menu']:
                value=row['states'][row['actual']]['obs'][selected]
                messages+= [dict(role='assistant',content=first['content']),
                    dict(role='user',content=f'Lookup {selected} returns: {value}. Give the final verdict and the certificate for the evidence now available. Return only verdict and certificate.')]
                session['second']=stage(key/'second.json',messages,row,model,seed+1000,False)
            save(key/'session.json',session)
            print(f'{part} {index+1}/{len(jobs)}: {rid} {arm} complete',flush=True)
    check_manifest(part,model)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['freeze','run'])
    parser.add_argument('part',choices=['dev','test'])
    parser.add_argument('model',choices=MODELS)
    args=parser.parse_args()
    (freeze if args.action=='freeze' else administer)(args.part,args.model)
