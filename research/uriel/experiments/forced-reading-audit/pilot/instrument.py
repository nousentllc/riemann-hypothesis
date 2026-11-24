"""Common local JSON adapter, saved request receipts, and model configuration."""
import datetime

import hashlib

import json

import urllib.request

from pathlib import Path

HERE=Path(__file__).resolve().parent

ROOT=HERE.parent

MODELS={'gptoss': {'tag': 'gpt-oss:20b', 'digest': '17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7', 'max_tokens': 2048, 'think': 'low'}}

def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temp.replace(path)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

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
