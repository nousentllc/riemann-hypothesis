"""Administer preregistered workflows. The second call gets only the actual first answer and the original evidence."""
import argparse
import fcntl
import json
import random
from collections import Counter
from instrument import HERE, ROOT, MODEL, SERVER, TIMEOUT_SECONDS, hash_request, digest, now, request_payload, save, stage, verify_model

SEED = 2026112467
ARMS = ('direct','label_first')
ROWS = ROOT/'circuits/records.json'
FINAL = 'Both readings have already been supplied. Return only the JSON fields verdict and certificate.'
SYSTEM = (HERE/'method.txt').read_text().strip()

def read(p):
    return json.loads(p.read_bytes())

def survivors(row):
    return {sid for sid,s in row['states'].items() if s['initial']==row['initial_reading']
            and s['obs'][row['meter']]==row['reading']}

def label_question(row):
    a,b=row['survivors']
    return (f'Before giving any verdict, report the target_current_above_threshold label for each displayed survivor. '
            f'Return only a JSON object with keys {a} and {b}, each having value Y or N. The verdict will be requested separately.')

def render(row,mode):
    meters = list(row["menu"])
    lines = [
        row["description"],
        f"Question: is the signed current of {row['signed_branch']} > {row['target_threshold']} A?",
        "Initial comparator: " + row["initial_description"],
        "Other comparators: " + " | ".join(f"{k}: {row['menu'][k]}" for k in meters),
        "H means a comparator condition holds and L means it fails. All currents are exact amperes. The last column gives the result of the named current comparison in each setting.",
        "In the mark column, * explicitly identifies a setting compatible with both observed readings. A dot means no marker is supplied for that row.",
        "mark ID stu target_current initial " + " ".join(meters) + " target_current_above_threshold",
    ]
    kept = survivors(row)
    for sid in row["state_order"]:
        if sid not in kept:
            continue
        state = row["states"][sid]
        marker = "."
        lines.append(" ".join([marker,sid,state["bits"],state["target_current"],state["initial"],
                               *(state["obs"][m] for m in meters),"Y" if state["answer"] else "N"]))
    lines.extend(["",f"Observed readings: initial = {row['initial_reading']}; {row['meter']} = {row['reading']}.",
        "The table includes every setting compatible with both readings. Use both readings when identifying which settings remain possible.",
        "Y means the named claim holds in every compatible setting. N means it fails in every compatible setting. U means both answers are possible.",
        "For Y or N, list all and only the compatible IDs. For U, list exactly two compatible IDs with opposite target answers. Use no duplicate IDs.",
        "Both readings have already been supplied. Return only the JSON fields verdict and certificate."])
    if mode=='labels':
        lines[-1] = label_question(row)
    return "\n".join(lines)

def initial(rid, row, stage_name):
    return [dict(role='system',content=SYSTEM),
            dict(role='user',content=(HERE/'prompts'/f'{rid}.{stage_name}.txt').read_text())]

def followup(messages, content):
    return [*messages,dict(role='assistant',content=content),dict(role='user',content=FINAL)]

def order(rows):
    rng=random.Random(SEED)
    families=sorted({r['family'] for r in rows.values()})
    rng.shuffle(families)
    waves=[[],[]]
    for rid,row in sorted(rows.items()):
        labels=''.join('Y' if row['states'][s]['answer'] else 'N' for s in row['survivors'])
        rank=['YY','NN','YN','NY'].index(labels)
        j=families.index(row['family'])
        first=(rank+j)%2
        for wave,arm in zip(waves,ARMS if first==0 else ARMS[::-1]):
            wave.append(dict(record=rid,arm=arm))
    for wave in waves:
        rng.shuffle(wave)
    return waves[0]+waves[1]

def freeze():
    path=HERE/'freeze.json'
    if path.exists() or (HERE/'observed').exists():
        raise ValueError('Already frozen or dispatched')
    rows=read(ROWS)
    (HERE/'prompts').mkdir(exist_ok=True)
    for rid,row in rows.items():
        for mode in ('direct','labels'):
            (HERE/'prompts'/f'{rid}.{mode}.txt').write_text(render(row,mode))
    jobs=order(rows)
    for job in jobs:
        rid,arm=job['record'],job['arm']
        row=rows[rid]
        seed=SEED+sorted(rows).index(rid)
        stage_name='direct' if arm=='direct' else 'labels'
        messages=initial(rid,row,stage_name)
        job['first_request_hash']=hash_request(request_payload(messages,row,seed+(1000 if stage_name=='labels' else 0),stage_name))
        if stage_name=='labels':
            template=followup(messages,'{VERBATIM_VISIBLE_LABEL_RESPONSE}')
            job['verdict_template_hash']=hash_request(request_payload(template,row,seed,'verdict'))
    save(HERE/'order.json',jobs)
    paths=[p for sub in ('circuits','pilot') for p in (ROOT/sub).rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    paths.extend([ROOT/'PROTOCOL.md'])
    save(path,dict(at=now(),seed=SEED,model=MODEL,ollama=SERVER,socket_timeout_seconds=TIMEOUT_SECONDS,
                   records=24,workflows=48,maximum_inferences=72,paid_api_cap_usd=0,
                   sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(paths)}))

def verify():
    for name,h in read(HERE/'freeze.json')['sha256'].items():
        if digest(ROOT/name)!=h:
            raise ValueError('Frozen file changed: '+name)

def collect():
    verify()
    verify_model()
    rows=read(ROWS); jobs=read(HERE/'order.json')
    out=HERE/'observed';out.mkdir(exist_ok=True)
    with (out/'run.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        for index,job in enumerate(jobs,1):
            rid,arm=job['record'],job['arm']
            row=rows[rid]; seed=SEED+sorted(rows).index(rid)
            mode='direct' if arm=='direct' else 'labels'
            msgs=initial(rid,row,mode); directory=out/f'{rid}_{arm}'
            payload=request_payload(msgs,row,seed+(1000 if mode=='labels' else 0),mode)
            rec=stage(directory/mode/'response.json',payload,row,job['first_request_hash'],mode)
            if mode=='labels' and rec['status']=='ok':
                template=request_payload(followup(msgs,'{VERBATIM_VISIBLE_LABEL_RESPONSE}'),row,seed,'verdict')
                if hash_request(template)!=job['verdict_template_hash']:
                    raise ValueError('Drift in conditional verdict request')
                payload=request_payload(followup(msgs,rec['content']),row,seed,'verdict')
                rec=stage(directory/'verdict/response.json',payload,row,hash_request(payload),'verdict')
            print(f'{index}/{len(jobs)} {rid} {arm} {rec["status"]}',flush=True)
    verify();verify_model()

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    actions={'freeze':freeze,'verify':verify,'preflight':verify_model,'collect':collect}
    parser.add_argument('action',choices=actions)
    actions[parser.parse_args().action]()
