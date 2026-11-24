"""Freeze and administer the fresh, single-column circuit comparison."""
import argparse
import fcntl
import json
import random
from pathlib import Path

from instrument import HERE, ROOT, MODELS, digest, local, now, oracle, public_task, save, stage, validate

SEED = 2026112429
ARMS = ('raw', 'labeled')
RECORDS = ROOT / 'circuits' / 'records.json'


def render(row, arm):
    text = public_task(row)
    if arm == 'raw':
        return text
    lines = text.split('\n')
    idx = next(i for i,v in enumerate(lines) if v.startswith('ID stu target_current initial '))
    lines[idx] += ' target_current_above_threshold'
    for j in range(idx+1,idx+1+len(row['states'])):
        ident = lines[j].split()[0]
        lines[j] += ' Y' if row['states'][ident]['answer'] else ' N'
    return '\n'.join(lines)


def schedule(rows):
    rng = random.Random(SEED)
    families = sorted({r['family'] for r in rows.values()})
    rng.shuffle(families)
    waves = [[], []]
    for i, family in enumerate(families):
        pair = [(rid,oracle(row)['kind']) for rid,row in rows.items() if row['family']==family]
        if len(pair)!=2 or sum(k=='lookup' for _,k in pair)!=1:
            raise ValueError(f'Missing actionable/control pair for {family}')
        for rid, kind in pair:
            raw_first = (i%2==0) == (kind=='lookup')
            for wave, arm in enumerate(ARMS if raw_first else reversed(ARMS)):
                waves[wave].append(dict(record=rid,arm=arm))
    for wave in waves:
        rng.shuffle(wave)
    return waves[0]+waves[1]


def verify_model():
    if local('/api/version')['version'] != '0.40.4':
        raise ValueError('Ollama version differs from prior study')
    config = MODELS['gptoss']
    if not any(p['digest']==config['digest'] and p['name']==config['tag'] for p in local('/api/tags')['models']):
        raise ValueError('Registered model is unavailable')


def freeze():
    path = HERE/'freeze.json'
    if path.exists() or (HERE/'observed').exists():
        raise ValueError('Run or freeze already exists')
    rows = json.loads(RECORDS.read_text())
    if len(rows)!=12 or len({r['family'] for r in rows.values()})!=6:
        raise ValueError('Invalid panel size')
    stats=[]; positions=[]
    (HERE/'prompts').mkdir(exist_ok=True)
    for rid,row in rows.items():
        validate(row)
        state=oracle(row)
        stats.append((state['kind'],state['target']))
        if state['kind']=='lookup':
            if len(state['decisive'])!=1 or state['decisive']!=state['guaranteed']:
                raise ValueError('Actionable record must have one unique decisive option')
            positions.append(list(row['menu']).index(state['decisive'][0]))
        for arm in ARMS:
            (HERE/'prompts'/f'{rid}.{arm}.txt').write_text(render(row,arm))
    if sorted(positions)!=[0,0,1,1,2,2] or stats.count(('lookup','Y'))!=3 or stats.count(('lookup','N'))!=3:
        raise ValueError('Lookup balance mismatch')
    if sum(k=='settled' for k,_ in stats)!=3 or stats.count(('ambiguous','U'))!=3:
        raise ValueError('Control balance mismatch')
    verify_model()
    save(HERE/'order.json',schedule(rows))
    paths=[f for sub in ('circuits','pilot') for f in (ROOT/sub).rglob('*') if f.is_file() and not f.name.startswith('.') and '__pycache__' not in f.parts]
    # The auditor operates independently; the prompt, circuit inputs, scoring and runner are sealed here.
    save(path,dict(at=now(),seed=SEED,model=MODELS['gptoss'],ollama='0.40.4',paid_cap_usd=0,
                   sessions=24,max_requests=48,sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(paths)}))


def verify_frozen():
    manifest=json.loads((HERE/'freeze.json').read_text())
    for name,hh in manifest['sha256'].items():
        if digest(ROOT/name)!=hh:
            raise ValueError(f'Frozen bytes differ at {name}')


def administer():
    verify_frozen()
    verify_model()
    rows = json.loads(RECORDS.read_text()); jobs=json.loads((HERE/'order.json').read_text())
    folder=HERE/'observed'; folder.mkdir(exist_ok=True)
    with (folder/'run.lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for i,job in enumerate(jobs):
            rid,arm=job['record'],job['arm']
            row=rows[rid]; out=folder/f'{rid}_{arm}'
            seed=SEED+int(rid.rsplit('-',1)[1])
            messages=[dict(role='system',content=(HERE/'method.txt').read_text().strip()),
                      dict(role='user',content=(HERE/'prompts'/f'{rid}.{arm}.txt').read_text())]
            first=stage(out/'first.json',messages,row,'gptoss',seed,True)
            session=dict(record=rid,arm=arm,first=first)
            selected=(first.get('answer') or {}).get('lookup')
            if selected in row['menu']:
                value=row['states'][row['actual']]['obs'][selected]
                session['observation']=dict(item=selected,value=value)
                messages.extend([dict(role='assistant',content=first['content']),dict(role='user',content=f'Lookup {selected} returns: {value}. Give the final verdict and the certificate for the evidence now available. Return only verdict and certificate.')])
                session['second']=stage(out/'second.json',messages,row,'gptoss',seed+1000,False)
            save(out/'session.json',session)
            print(f'{i+1}/{len(jobs)} sessions complete',flush=True)
    verify_frozen()
    verify_model()


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('freeze','run','verify'))
    arg=parser.parse_args()
    {'freeze':freeze,'run':administer,'verify':verify_frozen}[arg.action]()
