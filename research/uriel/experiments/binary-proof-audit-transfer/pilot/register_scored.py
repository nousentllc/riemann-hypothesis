"""Freeze the scored-only observable-menu amendment, preserving the original development registry."""
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from domain import ROOT, HERE, SEED, MODELS, build_data, digest, save, schedule, oracle, validate
from run import frozen_paths, local, now

def scored_rows():
    original=build_data()
    sys.path.insert(0,str(ROOT/'formal'))
    try:
        from score_cases import build as amended
        variant=amended()
    finally:
        sys.path.pop(0)
    revised={(r['family'],r['variant']):r for r in variant['test']}
    rows={}
    fields=['family','variant','text','evidence','actual','eligible']
    for rid,old in original['test'].items():
        r={**revised[old['family'],old['variant']],'domain':'formal'} if old['domain']=='formal' else old
        validate(r)
        if any(old[k]!=r[k] for k in fields): raise ValueError('Unexpected changes to visible facts or objects')
        if {s:v['answer'] for s,v in r['states'].items()}!={s:v['answer'] for s,v in old['states'].items()}:
            raise ValueError('Changed formal truths')
        for k in ('initial','kind','target'):
            if oracle(r)[k]!=oracle(old)[k]: raise ValueError(f'Target stratum changed: {rid}, {k}')
        rows[rid]=r
    return rows

def main(model):
    rows=scored_rows()
    folder=HERE/'registry'/('test-'+model)
    if (folder/'FROZEN.json').exists():raise ValueError('Scored registry already frozen')
    decision=HERE/'development_decision.json'
    if not json.loads(decision.read_text())['ready_for_scored_run'] or json.loads(decision.read_text())['selected']!=model:
        raise ValueError('Development model not selected')
    files=[*frozen_paths(),Path(__file__).resolve(),decision,HERE/'MENU_AMENDMENT.md',
           ROOT/'formal/score_cases.py',ROOT/'formal/sources.json',ROOT/'formal/receipt.json',
           ROOT/'circuits/verification.json']
    files+=sorted((ROOT/'diagnostics').glob('*.json'))
    files+= [ROOT/'formal/score_views.py', ROOT/'formal/score_menu_receipt.json',ROOT/'diagnostics/audit.py',ROOT/'diagnostics/PROTOCOL.md',HERE/'verify_run.py']
    save(folder/'records.json',rows);save(folder/'order.json',schedule(rows,'test'))
    files+=[folder/'records.json',folder/'order.json']
    tags=local('/api/tags')['models']
    if not any(t['name']==MODELS[model]['tag'] and t['digest']==MODELS[model]['digest'] for t in tags):
        raise ValueError('Pinned model changed')
    save(folder/'FROZEN.json',dict(at=now(),seed=SEED,model=MODELS[model],ollama=local('/api/version')['version'],
        direct_api_spend_cap_usd=0,session_count=48,max_requests=96,
        sha256={str(p.relative_to(ROOT)):digest(p) for p in files}))
    print('48 scored sessions frozen with pinned instrument and key')

if __name__=='__main__':main(sys.argv[1])
