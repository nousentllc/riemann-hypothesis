"""Enumerate fixed shortcuts and public/secret projections. Reads no model output."""
from collections import Counter, defaultdict
import argparse
import importlib.util
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'pilot'))
from domain import label, oracle, public_task, remaining, score_session
from run import schema


def partition(r, q):
    cells=defaultdict(list)
    for s in r['eligible']:
        cells[r['states'][s]['obs'][q]].append(s)
    return list(cells.values())


def possible_labels(r):
    return {oracle({**r,'actual':s})['target'] for s in r['eligible']}


def policy(r, name):
    options=list(r['menu'])
    if name=='none':return 'NONE'
    if name.startswith('position'):return options[int(name[-1])-1]
    if name=='most_distinct':
        return max(options,key=lambda q:len(partition(r,q)))
    if name=='most_balanced':
        return min(options,key=lambda q:sum(len(g)**2 for g in partition(r,q)))
    if name=='expected_decision':
        return max(options,key=lambda q:sum(len(g) for g in partition(r,q) if label(r,g)!='U'))
    if name=='oracle':
        o=oracle(r)
        return o['guaranteed'][0] if o['kind']=='lookup' else 'NONE'
    raise ValueError(name)


def oracle_certificate(r, visible):
    verdict=label(r,visible)
    ids=visible if verdict!='U' else [
        next(s for s in visible if r['states'][s]['answer']==sign) for sign in (True,False)]
    return dict(verdict=verdict,certificate=ids)


def count_actions(records, name):
    passes, products = defaultdict(list),0
    for r in records:
        q=policy(r,name)
        a=oracle_certificate(r,r['eligible'])
        receipt={'first':{'answer':{**a,'lookup':q}}}
        if q!='NONE':
            receipt['second']={'answer':oracle_certificate(r,remaining(r,q))}
        judged=score_session(r,receipt)
        passes[r['family']].append(judged['pass_case'])
        products+=judged['productive']
    return dict(cases=sum(sum(v) for v in passes.values()),families=sum(all(v) for v in passes.values()),
                productive_lookups=products)


def modal(strings):
    freq=Counter(strings)
    return min(freq,key=lambda v:(-freq[v],v))


def stage_label_stats(records, which):
    answer=lambda r:oracle(r)[which]
    state_sign=lambda r,s:'Y' if r['states'][s]['answer'] else 'N'
    def by_vote(r):
        signs=[state_sign(r,s) for s in r['eligible']]
        return 'U' if signs.count('Y')==signs.count('N') else modal(signs)
    immediate={
        'always_Y':lambda r:'Y','always_N':lambda r:'N','always_U':lambda r:'U',
        'first_source_ID_sign':lambda r:state_sign(r,next(iter(r['states']))),
        'last_source_ID_sign':lambda r:state_sign(r,list(r['states'])[-1]),
        'lex_first_compatible_sign':lambda r:state_sign(r,min(r['eligible'])),
        'majority_compatible_tie_U':by_vote,
    }
    # In the formal packet the table uses source dictionary order, whereas
    # circuit packets sort the table rows lexicographically.
    immediate['first_printed_ID_sign']=lambda r:state_sign(r,next(iter(r['states'])) if r['domain']=='formal' else min(r['states']))
    immediate['last_printed_ID_sign']=lambda r:state_sign(r,list(r['states'])[-1] if r['domain']=='formal' else max(r['states']))
    shortcuts={k:sum(fn(r)==answer(r) for r in records) for k,fn in immediate.items()}
    def first_ordinal(r):
        display=list(r['states']) if r['domain']=='formal' else sorted(r['states'])
        return next(j for j,i in enumerate(display) if i in r['eligible'])
    features={
        'evidence_last_token':lambda r:r['evidence'].split()[-1],
        'eligible_size':lambda r:len(r['eligible']),
        'total_menu_description_chars':lambda r:sum(len(s) for s in r['menu'].values()),
        'first_menu_ID':lambda r:next(iter(r['menu'])),
        'first_eligible_row_ordinal':first_ordinal,
        'first_eligible_ID_character':lambda r:min(r['eligible'])[0]}
    leave={}
    for key,fn in features.items():
        matches=0
        for row in records:
            training=[r for r in records if r['family']!=row['family']]
            use=[r for r in training if fn(r)==fn(row)] or training
            matches+=modal([answer(r) for r in use])==answer(row)
        leave[key]=matches
    return dict(oracle_frequencies=dict(Counter(answer(r) for r in records)), label_only_fixed=shortcuts,
                leave_one_family_out_label_only=leave)


def projections(r):
    public=public_task(r)
    shapes=(schema(r,True),schema(r,False))
    fake={**r,'family':'SENTINEL_FAMILY','domain':'SENTINEL_DOMAIN','variant':'SENTINEL_VARIANT',
          'actual':'SENTINEL_ACTUAL','eligible':['SENTINEL_ELIGIBLE'],
          'states':{k:{'answer':'SENTINEL_TRUTH','obs':'SENTINEL_OUTCOMES'} for k in r['states']}}
    assert public_task(fake)==public and (schema(fake,True),schema(fake,False))==shapes
    return public,shapes


def load_heldout(domain, filename):
    path=ROOT/domain/filename
    spec=importlib.util.spec_from_file_location(domain+"_diagnostic_"+path.stem, path)
    mod=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=mod
    sys.path.insert(0,str(path.parent))
    try:
        spec.loader.exec_module(mod)
        return [{**r,"domain":domain} for r in mod.build()["test"]]
    finally:
        sys.path.remove(str(path.parent))


def do_audit(version="original"):
    names={"formal":("cases.py" if version=="original" else "score_cases.py"),"circuits":"cases.py"}
    src={d+str(i):r for d,name in names.items() for i,r in enumerate(load_heldout(d,name))}
    result={'version':version,'generators':{d:sha256((ROOT/d/name).read_bytes()).hexdigest() for d,name in names.items()},'records':len(src),'families':len({r['family'] for r in src.values()}),'by_domain':{}}
    seen=set()
    for d in ('circuits','formal'):
        rows=[r for r in src.values() if r['domain']==d]
        by_family=defaultdict(list)
        for r in rows:by_family[r['family']].append(r)
        exposure=[]
        for family,(r,s) in by_family.items():
            assert set(r['eligible']).isdisjoint(s['eligible'])
            assert set(r['eligible'])|set(s['eligible'])==set(r['states'])
            assert r['states']==s['states'] and r['text']==s['text'] and r['menu']==s['menu']
            pr,sr=projections(r);ps,ss=projections(s)
            assert sr==ss and pr.replace(r['evidence'],'EVIDENCE_SLOT')==ps.replace(s['evidence'],'EVIDENCE_SLOT')
            if r['domain']=='formal':
                # Disjoint visible rule lines for six formal holdouts.
                assert r['text'].splitlines()[1] not in seen
                seen.add(r['text'].splitlines()[1])
            for row in (r,s):
                o=oracle(row)
                kinds={oracle({**row,'actual':state})['kind'] for state in row['eligible']}
                assert kinds=={o['kind']}
                if o['kind']=='lookup':
                    assert len(o['guaranteed'])==1
                if o['kind']=='ambiguous':
                    assert possible_labels(row)=={'U'}
                exposure.append(dict(family=family,variant=row['variant'],kind=o['kind'],
                                    eligible_count=len(row['eligible']),
                                    target_across_actuals=sorted(possible_labels(row)),
                                    option_cells=[len(partition(row,q)) for q in row['menu']],
                                    useful_positions=([list(row['menu']).index(q)+1 for q in o['guaranteed']]
                                                      if o['kind']=='lookup' else [])))
        acts={p:count_actions(rows,p) for p in ('none','position1','position2','position3','most_distinct','most_balanced','expected_decision','oracle')}
        assert acts['oracle']=={'cases':12,'families':6,'productive_lookups':4}
        result['by_domain'][d]=dict(projection_invariant=len(rows),pairs_single_visible_change=len(by_family),
                                      action_policy_with_perfect_reader=acts,
                                      initial_label_diagnostics=stage_label_stats(rows,'initial'),
                                      final_label_diagnostics=stage_label_stats(rows,'target'),finite_table=exposure)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--version',choices=('original','revised'),default='original')
    print(json.dumps(do_audit(parser.parse_args().version),indent=2,sort_keys=True))
