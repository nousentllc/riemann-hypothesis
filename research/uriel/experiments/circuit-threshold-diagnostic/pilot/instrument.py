"""Finite packet rendering, evidence oracle and local inference. Inherited functions retain the prior instrument semantics."""
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

def label(row, survivors):
    signs = {row['states'][i]['answer'] for i in survivors}
    if not signs or any(type(s) is not bool for s in signs):
        raise ValueError('Missing or invalid state label')
    return 'U' if len(signs)==2 else ('Y' if True in signs else 'N')

def remaining(row, item=None, value=None):
    if item is None or item == 'NONE':
        return list(row['eligible'])
    if value is None:
        value = row['states'][row['actual']]['obs'][item]
    return [s for s in row['eligible'] if row['states'][s]['obs'][item]==value]

def oracle(row):
    before = label(row,row['eligible'])
    single = [item for item in row['menu'] if label(row,remaining(row,item))!='U']
    all_outcomes = []
    for item in row['menu']:
        values = {row['states'][s]['obs'][item] for s in row['eligible']}
        if all(label(row, remaining(row,item,v))!='U' for v in values):
            all_outcomes.append(item)
    target = before if before!='U' or not single else label(row,[row['actual']])
    kind = 'settled' if before!='U' else ('lookup' if single else 'ambiguous')
    return dict(initial=before,target=target,kind=kind,decisive=single,guaranteed=all_outcomes)

def validate(row):
    for key in ('family','variant','text','evidence'):
        if not isinstance(row[key],str) or not row[key].strip(): raise ValueError(key)
    allowed = row['eligible']
    if len(allowed)!=len(set(allowed)) or row['actual'] not in allowed or not set(allowed)<=row['states'].keys():
        raise ValueError('Eligible set inconsistent')
    if 'NONE' in row['menu'] or not row['menu']: raise ValueError('Invalid menu')
    for state in row['states'].values():
        if type(state['answer']) is not bool or state['obs'].keys()!=row['menu'].keys():
            raise ValueError('Invalid state or observation keys')
        if any(not isinstance(v,str) for v in state['obs'].values()): raise ValueError('Invalid lookup value')

def public_task(row):
    menu='\n'.join(f'{i}: {s}' for i,s in row['menu'].items())
    return (row['text']+'\n\nObserved now:\n'+row['evidence']+'\n\nOptional lookup menu:\n'+menu+
        '\n\nUse only the packet. Y means the named claim holds in every compatible state, N means it fails in every compatible state, and U means both outcomes are possible. '+
        'Give the initial verdict and certificate before using a lookup. For Y or N list ALL and ONLY the compatible state IDs, with no duplicates. For U list exactly TWO compatible state IDs that give opposite answers. '+
        'Choose at most one lookup to obtain the strongest verdict attainable, or NONE to submit this as your final answer. Return the JSON fields verdict, certificate, lookup.')

def score_answer(row, answer, survivors):
    truth=label(row,survivors)
    answer = answer or {}
    v=answer.get('verdict')
    cert=answer.get('certificate',[])
    if not isinstance(cert,list) or not all(isinstance(s,str) for s in cert): cert=[]
    valid=(v==truth and len(set(cert))==len(cert) and set(cert)<=set(survivors))
    if valid:
        valid=(len(cert)==2 and label(row,cert)=='U') if v=='U' else set(cert)==set(survivors)
    return dict(verdict=v,expected=truth,certified=valid,licensed=v==truth,
                unsupported=v in ('Y','N') and v!=truth,
                guessed=v in ('Y','N') and truth=='U',wrong_sign=v in ('Y','N') and truth in ('Y','N') and v!=truth)

def score_session(row, receipt):
    first=receipt.get('first',{}).get('answer')
    first_score=score_answer(row,first,remaining(row))
    item=first.get('lookup') if first else None
    used=item in row['menu']
    survivors=remaining(row,item) if used else remaining(row)
    last=receipt.get('second',{}).get('answer') if used else first
    last_score=score_answer(row,last,survivors)
    target=oracle(row)
    return dict(initial=first_score,final=last_score,used=item,kind=target['kind'],target=target['target'],
      pass_case=bool(last_score['certified'] and last_score['verdict']==target['target']),
      productive=bool(used and target['initial']=='U' and last_score['expected']!='U'),
      missed_resolvable=bool(target['target']!='U' and last_score['verdict']!=target['target']),
      unsupported=int(first_score['unsupported'])+int(used and last_score['unsupported']),
      unnecessary_initial_abstention=bool(target['initial']!='U' and first_score['verdict']=='U'))

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
