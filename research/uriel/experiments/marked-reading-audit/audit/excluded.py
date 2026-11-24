"""Audit excluded witnesses, marked/filter crossovers, and refuting IDs on mixed twins."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARMS = ('unmarked','marked','filtered')
CATEGORIES = ('initial_only','second_only','neither')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def implication(ids, positive):
    if not ids:
        return None
    n = len(set(ids) & positive)
    return 'N' if n==0 else 'Y' if n==len(set(ids)) else 'U'


def score(oracle, answer):
    live = set(oracle['joint'])
    positive = set(oracle['target_yes'])
    first = set(oracle['initial_only'])
    second = set(oracle['second_only'])
    require(first & second == live and len(live)==2, 'Invalid two-observation oracle')
    true_verdict = implication(live,positive)
    require(true_verdict==oracle['verdict'], 'Oracle verdict disagreement')
    if answer is None:
        return dict(verdict=None,submitted=None,omitted=None,extra=None,duplicate_count=None,
                    exact_ids=False,verdict_matches=False,certified=False,own_label_verdict=None,
                    own_label_coherence=None,category='no_completed_answer',excluded_occurrences=[])
    ids=answer['certificate']
    require(1<=len(ids)<=8 and all(s in oracle['schema_order'] for s in ids), 'Out-of-grammar certificate')
    verdict=answer['verdict']
    require(verdict in ('Y','N','U'), 'Out-of-grammar verdict')
    kept=set(ids)
    own=implication(kept,positive)
    extra=sorted(kept-live)
    omitted=sorted(live-kept)
    duplicates=len(ids)-len(kept)
    exact=not (extra or omitted or duplicates)
    matches=verdict==true_verdict
    excluded=[dict(id=s,category='initial_only' if s in first else 'second_only' if s in second else 'neither')
              for s in ids if s not in live]
    tag = ('certified' if matches else 'verdict_defect_only') if exact else ('witness_defect_only' if matches else 'both_defects')
    return dict(verdict=verdict,submitted=ids,omitted=omitted,extra=extra,duplicate_count=duplicates,exact_ids=exact,
                verdict_matches=matches,certified=exact and matches,own_label_verdict=own,own_label_coherence=own==verdict,
                category=tag,excluded_occurrences=excluded)


def synthetic_test():
    first={'A','B','C','D'}
    second={'A','B','E','F'}
    ids='ABCDEFGH'
    total=0
    for positive in ({'A','C','E','G'}, {'A','B','C','D'}, {'C','D','E','F'}):
        expected='U' if ('A' in positive)!=('B' in positive) else 'Y' if 'A' in positive else 'N'
        oracle=dict(joint=['A','B'],target_yes=sorted(positive),initial_only=sorted(first),second_only=sorted(second),
                    verdict=expected,schema_order=list(ids))
        for n in range(1,9):
            for batch in combinations(ids,n):
                sf=set(batch)
                tags = dict(C='initial_only',D='initial_only',E='second_only',F='second_only',G='neither',H='neither')
                occurrence=[dict(id=s,category=tags[s]) for s in batch if s in tags]
                own = 'Y' if sf<=positive else 'N' if sf.isdisjoint(positive) else 'U'
                for sign in ('Y','N','U'):
                    out=score(oracle,dict(verdict=sign,certificate=list(batch)))
                    require(out['excluded_occurrences']==occurrence and set(out['omitted'])=={'A','B'}-sf and
                            out['own_label_verdict']==own and out['own_label_coherence']==(own==sign) and
                            out['exact_ids']==(batch==('A','B')) and out['verdict_matches']==(sign==expected) and
                            out['certified']==(batch==('A','B') and sign==expected), 'Synthetic enumeration failed')
                    total+=1
    repeated=score(oracle,dict(verdict='N',certificate=['A','B','A','C','C','F','H']))
    require(not repeated['exact_ids'] and repeated['duplicate_count']==2 and len(repeated['excluded_occurrences'])==4,
            'Duplicate counting failed')
    missing=score(oracle,None)
    require(missing['category']=='no_completed_answer' and missing['own_label_coherence'] is None
            and missing['omitted'] is None and not missing['certified'], 'Missing data incorrectly treated as a selection')
    return total


def run(root):
    pilot=root/'pilot'
    audit=load(root/'audit'/'displays.json')
    oracle=audit['record_oracle']
    paths={(rid,arm):pilot/'observed'/f'{rid}_{arm}'/'response.json' for rid in oracle for arm in ARMS}
    require(len(paths)==72 and all(p.is_file() for p in paths.values()) and (pilot/'results'/'cases.csv').is_file(),
            'Wait for all 72 receipts and the scored table before examining outcomes')
    scores={}
    summaries={}
    for arm in ARMS:
        occurrences=Counter()
        responses=Counter()
        category_counts=Counter()
        completed=any_extra=all_ids=extra_ids=0
        for rid,c in sorted(oracle.items()):
            raw=load(paths[rid,arm])
            require(raw['request_sha256']==audit['request_sha256'][rid][arm],'Receipt outside reconstructed manifest')
            ans=None
            if raw['status']=='ok':
                require(raw['usage']['done_reason']=='stop','Incomplete response counted as valid')
                ans=json.loads(raw['content'])
                require(isinstance(ans,dict) and set(ans)=={'verdict','certificate'} and ans==raw['answer'],'Parsed answer disagreement')
                completed+=1
            else:
                require(raw['answer'] is None,'Nonterminal answer present')
            s=score(c,ans)
            s['status']=raw['status']
            scores[rid,arm]=s
            categories=[entry['category'] for entry in s['excluded_occurrences']]
            occurrences.update(categories)
            responses.update(set(categories))
            any_extra+=bool(categories)
            all_ids+=len(s['submitted'] or [])
            extra_ids+=sum(x not in c['joint'] for x in (s['submitted'] or []))
            category_counts[s['category']]+=1
        require(sum(occurrences.values())==extra_ids, 'Excluded occurrence counts differ')
        summaries[arm]=dict(attempted=len(oracle),completed=completed,submitted_id_occurrences=all_ids,
                            excluded_id_occurrences=extra_ids,responses_with_any_excluded_id=any_extra,
                            occurrences_by_category={k:occurrences[k] for k in CATEGORIES},
                            responses_by_category_nonexclusive={k:responses[k] for k in CATEGORIES},
                            response_category_counts=dict(sorted(category_counts.items())))
    discordant=[]
    false_definite={arm:[] for arm in ARMS}
    for rid,c in sorted(oracle.items()):
        m,f=scores[rid,'marked'],scores[rid,'filtered']
        if m['certified']!=f['certified']:
            better,worse=('marked','filtered') if m['certified'] else ('filtered','marked')
            discordant.append(dict(record=rid,layout=c['family'],kind=c['kind'],warranted=c['verdict'],
                                   joint=c['joint'],certified_display=better,failed_display=worse,
                                   failed=scores[rid,worse],successful=scores[rid,better]))
        if c['verdict']!='U':
            continue
        twin=[t for t,v in oracle.items() if t!=rid and v['family']==c['family'] and v['meter']==c['meter']
              and v['verdict']=='U' and v['reading']!=c['reading']]
        require(len(twin)==1 and set(c['joint']).isdisjoint(oracle[twin[0]]['joint']), 'Invalid mixed twin')
        for arm in ARMS:
            s=scores[rid,arm]
            if s['verdict'] not in ('Y','N'):
                continue
            pos=set(c['target_yes'])
            pro,anti=sorted(c['joint'],key=lambda x:int((x in pos)!=(s['verdict']=='Y')))
            require((pro in pos)!=(anti in pos), 'Missing physical counterexample')
            rhs=scores[twin[0],arm]
            false_definite[arm].append(dict(record=rid,layout=c['family'],meter=c['meter'],reading=c['reading'],returned=s['verdict'],
                            compatible_supporting_id=pro,compatible_refuting_id=anti,cited_support=pro in s['submitted'],
                            cited_refutation=anti in s['submitted'],submitted=s['submitted'],own_label_coherence=s['own_label_coherence'],
                            other_mixed_record=twin[0],other_reading=oracle[twin[0]]['reading'],other_joint=oracle[twin[0]]['joint'],
                            other_returned=rhs['verdict'],other_submitted=rhs['submitted'],other_certified=rhs['certified']))
    for arm,details in false_definite.items():
        affected=Counter(v['layout'] for v in details)
        summaries[arm]['false_definites_on_mixed']=dict(mixed_records=12,mixed_layouts=6,
                                     records=len(details),layouts=len(affected),both_records_on_layout=sum(n==2 for n in affected.values()),
                                     cited_refuting_id=sum(x['cited_refutation'] for x in details),
                                     omitted_refuting_id=sum(not x['cited_refutation'] for x in details))
    primary=load(pilot/'results'/'summary.json')
    for arm in ARMS:
        s=summaries[arm]; tally=primary['totals'][arm]
        require(s['completed']==tally['parseable'] and s['response_category_counts'].get('certified',0)==tally['certified']
                and s['false_definites_on_mixed']['records']==tally['unsupported_ambiguous'],'Official totals differ')
    contrast=primary['comparisons']['marked_vs_filtered']['cases']
    require(len(discordant)==contrast['left_only']+contrast['right_only'] and
            {d['record'] for d in discordant if d['certified_display']=='marked'}==set(contrast['left_only_ids']),
            'Official discordances differ')
    return dict(synthetic_unique_subset_verdict_cases=synthetic_test(),summaries=summaries,
                marked_filtered_unilateral_certifications=discordant,false_definites_on_mixed=false_definite,
                all_cases={f'{r}_{a}':s for (r,a),s in scores.items()})


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('test','write','verify'))
    mode=parser.parse_args().mode
    if mode=='test':
        print(synthetic_test(),'exhaustive joint-set/verdict cases, plus duplicate and missing cases')
    else:
        result=run(ROOT)
        path=ROOT/'audit'/'excluded.json'
        text=json.dumps(result,sort_keys=True,indent=2)+'\n'
        if mode=='write':
            path.write_text(text)
        else:
            require(path.read_text()==text, 'Archived supplement differs')
        print(json.dumps(result['summaries'],indent=2))
