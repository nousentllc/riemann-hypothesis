"""Freeze and administer one label checkpoint with two independent binary continuations."""
import argparse
from collections import Counter
import fcntl
import json
import random

from instrument import HERE, ROOT, MODEL, SERVER, TIMEOUT_SECONDS, digest, hash_request, now, request_payload, save, stage, verify_model

SEED = 2026112479
ROWS = ROOT/'circuits/records.json'
SYSTEM = (HERE/'method.txt').read_text().strip()
SLOT = '{VERBATIM_VISIBLE_LABEL_RESPONSE}'
QUERIES = {
    'any': 'Is the target label Y for at least one of the two survivors?',
    'both': 'Is the target label Y for both of the two survivors?',
}
ANSWER_FORMAT = ' Return only the JSON field answer, using Y for yes and N for no.'


def read(p):
    return json.loads(p.read_bytes())


def render(row):
    meters = list(row['menu'])
    a,b = row['survivors']
    lines = [
        row['description'],
        f"The target label is Y if the signed current of {row['signed_branch']} > {row['target_threshold']} A, and N otherwise.",
        'Initial comparator: '+row['initial_description'],
        'Other comparators: '+' | '.join(m+': '+row['menu'][m] for m in meters),
        'H means a comparator condition holds and L means it fails. All currents are exact amperes.',
        'ID stu target_current initial '+' '.join(meters)+' target_label',
    ]
    for sid in (a,b):
        state = row['states'][sid]
        lines.append(' '.join([sid,state['bits'],state['target_current'],state['initial'],
                               *(state['obs'][m] for m in meters),'Y' if state['answer'] else 'N']))
    lines.extend(['',f"Observed readings: initial = {row['initial_reading']}; {row['meter']} = {row['reading']}.",
                  'The table shows exactly the two survivors compatible with the observed readings.',
                  f'Report the target label for each survivor. Return only a JSON object with keys {a} and {b}, each having value Y or N.'])
    return '\n'.join(lines)


def prefix(rid):
    return [{'role':'system','content':SYSTEM},
            {'role':'user','content':(HERE/'prompts'/f'{rid}.labels.txt').read_text()}]


def continuation(messages, visible, name):
    return [*messages,{'role':'assistant','content':visible},
            {'role':'user','content':QUERIES[name]+ANSWER_FORMAT}]


def make_order(rows):
    rng = random.Random(SEED)
    families = sorted({r['family'] for r in rows.values()})
    rng.shuffle(families)
    jobs = []
    for idx,(rid,row) in enumerate(sorted(rows.items())):
        pattern = ''.join('Y' if row['states'][s]['answer'] else 'N' for s in row['survivors'])
        pos = ('YY','NN','YN','NY').index(pattern)
        flip = (families.index(row['family'])+pos)%2
        jobs.append(dict(record=rid,query_order=['both','any'] if flip else ['any','both'],seed=SEED+idx))
    rng.shuffle(jobs)
    return jobs


def check_panel(rows, jobs):
    assert len(rows)==24 and len(jobs)==24 and set(rows)=={j['record'] for j in jobs}
    ords=Counter(); layout=Counter()
    for job in jobs:
        row=rows[job['record']]
        live=[s for s in row['state_order'] if row['states'][s]['initial']==row['initial_reading']
              and row['states'][s]['obs'][row['meter']]==row['reading']]
        assert live==row['survivors'] and len(live)==2
        pattern=''.join('Y' if row['states'][s]['answer'] else 'N' for s in live)
        ords[pattern,job['query_order'][0]]+=1
        layout[row['family'],job['query_order'][0]]+=1
    assert ords=={(p,q):3 for p in ('YY','NN','YN','NY') for q in QUERIES}
    assert len(layout)==12 and set(layout.values())=={2}


def freeze():
    path=HERE/'freeze.json'
    if path.exists() or (HERE/'observed').exists():
        raise ValueError('Existing freeze or observations')
    verify_model()
    rows=read(ROWS)
    (HERE/'prompts').mkdir(exist_ok=True)
    for rid,row in rows.items():
        (HERE/'prompts'/f'{rid}.labels.txt').write_text(render(row))
    jobs=make_order(rows)
    check_panel(rows,jobs)
    for job in jobs:
        rid=job['record'];row=rows[rid];seed=job['seed'];msgs=prefix(rid)
        job['labels_request_sha256']=hash_request(request_payload(msgs,row,seed+1000,'labels'))
        job['query_template_sha256']={q:hash_request(request_payload(continuation(msgs,SLOT,q),row,seed,q)) for q in QUERIES}
    save(HERE/'order.json',jobs)
    inputs=[p for sub in ('circuits','pilot') for p in (ROOT/sub).rglob('*')
            if p.is_file() and '__pycache__' not in p.parts and not p.name.startswith('.')]
    inputs.append(ROOT/'PROTOCOL.md')
    save(path,dict(at=now(),seed=SEED,model=MODEL,ollama=SERVER,records=24,maximum_inferences=72,
                   socket_timeout_seconds=TIMEOUT_SECONDS,paid_api_cap_usd=0,
                   sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(inputs)}))


def verify():
    for n,h in read(HERE/'freeze.json')['sha256'].items():
        if digest(ROOT/n)!=h:raise ValueError('Frozen input changed: '+n)


def collect():
    verify()
    verify_model()
    rows=read(ROWS);jobs=read(HERE/'order.json')
    root=HERE/'observed';root.mkdir(exist_ok=True)
    with (root/'run.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for i,job in enumerate(jobs,1):
            rid=job['record'];row=rows[rid];seed=job['seed'];msgs=prefix(rid)
            base=request_payload(msgs,row,seed+1000,'labels')
            label=stage(root/rid/'labels/response.json',base,row,job['labels_request_sha256'],'labels')
            statuses={'labels':label['status']}
            if label['status']=='ok':
                for q in job['query_order']:
                    template=request_payload(continuation(msgs,SLOT,q),row,seed,q)
                    if hash_request(template)!=job['query_template_sha256'][q]:
                        raise ValueError('Frozen sibling template changed')
                    resolved=request_payload(continuation(msgs,label['content'],q),row,seed,q)
                    receipt=stage(root/rid/q/'response.json',resolved,row,hash_request(resolved),q)
                    statuses[q]=receipt['status']
            print(f'{i}/24 {rid} {statuses}',flush=True)
    verify();verify_model()


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    actions={'freeze':freeze,'verify':verify,'preflight':verify_model,'collect':collect}
    parser.add_argument('action',choices=actions)
    actions[parser.parse_args().action]()
