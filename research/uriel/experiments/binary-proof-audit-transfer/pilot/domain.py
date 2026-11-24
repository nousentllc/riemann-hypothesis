"""Public projection, finite-state oracle, and independent-session certificate scoring."""
from pathlib import Path
import hashlib
import importlib.util
import json
import random
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODELS = {
    'qwen': dict(tag='qwen2.5:3b', digest='357c53fb659c5076de1d65ccb0b397446227b71a42be9d1603d46168015c9e4b',
                 max_tokens=512),
    'gptoss': dict(tag='gpt-oss:20b', digest='17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7',
                   max_tokens=2048, think='low'),
}
ARMS = ('general','method')
SEED = 2026112417

def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temp.replace(path)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def obtain(domain):
    directory = ROOT/domain
    path = directory/'cases.py'
    sys.path.insert(0, str(directory))
    try:
        name = domain+'_packets'
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
        return module.build()
    finally:
        sys.path.remove(str(directory))

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

def build_data():
    output = {'dev':{}, 'test':{}}
    for domain in ('circuits','formal'):
        rows = obtain(domain)
        for part in output:
            ordered=sorted(rows[part],key=lambda r:(r['family'],r['variant']))
            families = sorted({r['family'] for r in ordered})
            if part=='test' and len(families)!=6: raise ValueError('Expected six families')
            if part=='dev' and len(families)<2: raise ValueError('Expected two disjoint dev families')
            for family in families[:2] if part=='dev' else families:
                twins = [r for r in ordered if r['family']==family]
                if part=='test' and (len(twins)!=2 or len({r['variant'] for r in twins})!=2):
                    raise ValueError('Expected twin variants')
                for r in twins[:1] if part=='dev' else twins:
                    validate(r)
                    idx = f"{domain}-{len(output[part]):02d}"
                    output[part][idx]={**r,'domain':domain}
        if {r['family'] for r in rows['dev']}&{r['family'] for r in rows['test']}:
            raise ValueError('Development family reused')
    for domain in ('circuits','formal'):
        tiers = [oracle(r) for r in output['test'].values() if r['domain']==domain]
        if {t['kind'] for t in tiers}!={'settled','lookup','ambiguous'} or {t['target'] for t in tiers}!={'Y','N','U'}:
            raise ValueError(f'Panel missing required strata in {domain}')
    return output

def schedule(rows, part):
    jobs=[dict(record=rid, arm=arm) for rid in rows for arm in ARMS]
    random.Random(SEED+(part=='dev')).shuffle(jobs)
    return jobs

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
