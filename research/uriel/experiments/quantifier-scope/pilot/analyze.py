"""Score the 24 preregistered records using exact physical truth and visible outputs."""
import csv
from collections import Counter
from fractions import Fraction
from itertools import product

from instrument import HERE, ROOT, parse_answer, save
from run import read, verify

STAGES = ('labels', 'any', 'both')
SIGNS = ('YY', 'YN', 'NY', 'NN')
MAPS = {
    'scope': lambda p: ('Y' if 'Y' in p else 'N') + ('Y' if p == 'YY' else 'N'),
    'existence_twice': lambda p: ('Y' if 'Y' in p else 'N') * 2,
    'universal_twice': lambda p: ('Y' if p == 'YY' else 'N') * 2,
    'reversed_scope': lambda p: MAPS['scope'](p)[::-1],
    'always_yes': lambda p: 'YY',
    'always_no': lambda p: 'NN',
    'first_row_twice': lambda p: p[0] * 2,
    'second_row_twice': lambda p: p[1] * 2,
}


def case_truth(row):
    live = [sid for sid in row['state_order'] if row['states'][sid]['initial'] == row['initial_reading']
            and row['states'][sid]['obs'][row['meter']] == row['reading']]
    if live != row['survivors'] or len(live) != 2:
        raise ValueError('Survivor mismatch')
    labels = ''.join('Y' if Fraction(row['states'][sid]['target_current']) > Fraction(row['target_threshold'])
                     else 'N' for sid in live)
    return live, labels


def load_receipt(rid, stage, row):
    rec = read(HERE/'observed'/rid/stage/'response.json')
    if rec['status'] == 'ok':
        parsed = parse_answer(rec['content'], row, stage)
        if parsed is None or parsed != rec['answer'] or rec['usage']['done_reason'] != 'stop':
            raise ValueError(f'Invalid accepted receipt on {rid}/{stage}')
    elif rec['answer'] is not None:
        raise ValueError('Unexpected parsed answer on failure')
    return rec


def classify(job, row, receipts):
    ids, pattern = case_truth(row)
    checkpoint = receipts['labels']
    labels = checkpoint['answer']
    report = ''.join(labels[sid] for sid in ids) if labels else ''
    expected = MAPS['scope'](pattern)
    proposed = MAPS['scope'](report) if report else ''
    actual = ''
    out = dict(record=job['record'], family=row['family'], pattern=pattern, first=job['query_order'][0],
               first_id=ids[0], second_id=ids[1], reported_labels=report,
               label_hits=sum(a==b for a,b in zip(pattern,report)), exact_labels=int(report == pattern),
               labels_status=checkpoint['status'])
    for i,q in enumerate(('any','both')):
        rec = receipts.get(q)
        answer = rec['answer']['answer'] if rec and rec['answer'] is not None else ''
        actual += answer or '-'
        out[q+'_truth'] = expected[i]
        out[q+'_answer'] = answer
        out[q+'_status'] = rec['status'] if rec else 'gated'
        out[q+'_correct'] = int(answer == expected[i])
        out[q+'_reported_truth'] = proposed[i] if proposed else ''
        out[q+'_coherent'] = int(answer == proposed[i]) if proposed and answer else ''
    out.update(response_pair=actual, complete=int('-' not in actual), joint_correct=int(actual==expected))
    return out


def counts(values):
    return dict(sorted(Counter(values).items()))


def aggregate(cases):
    signatures = Counter(c['response_pair'] for c in cases)
    return dict(n=len(cases), complete=sum(c['complete'] for c in cases),
                signatures={s:signatures[s] for s in SIGNS},
                partials={s:n for s,n in sorted(signatures.items()) if '-' in s},
                joint_correct=sum(c['joint_correct'] for c in cases),
                branches={q:{'delivered':sum(bool(c[q+'_answer']) for c in cases),
                             'physically_correct':sum(c[q+'_correct'] for c in cases),
                             'consistent_with_report':sum(c[q+'_coherent']==1 for c in cases)}
                          for q in ('any','both')})


def bounds(pairs, target):
    lower = sum(p == target for p in pairs)
    upper = sum(all(s=='-' or s==t for s,t in zip(pair,target)) for pair in pairs)
    return [lower,upper]


def analyze():
    verify()
    records=read(ROOT/'circuits/records.json')
    jobs=read(HERE/'order.json')
    cases=[]; receipts={s:[] for s in STAGES}
    for job in jobs:
        rid=job['record']; row=records[rid]
        observed={'labels':load_receipt(rid,'labels',row)}
        if observed['labels']['status']=='ok':
            for q in ('any','both'):
                observed[q]=load_receipt(rid,q,row)
        elif any((HERE/'observed'/rid/q).exists() for q in ('any','both')):
            raise ValueError('Gated checkpoint with a child')
        for s,rec in observed.items():
            receipts[s].append(rec)
        cases.append(classify(job,row,observed))
    mixed=[c for c in cases if c['pattern'] in ('YN','NY')]
    controls=[c for c in cases if c not in mixed]
    def where(rows, key, value):
        return [c for c in rows if c[key]==value]
    summary={
        'all':aggregate(cases),
        'mixed':aggregate(mixed),
        'mixed_exact_complete':aggregate([c for c in mixed if c['complete'] and c['exact_labels']]),
        'mixed_inaccurate_checkpoint':aggregate([c for c in mixed if c['reported_labels'] and not c['exact_labels']]),
        'mixed_missing_checkpoint':aggregate([c for c in mixed if not c['reported_labels']]),
        'mixed_signature_attainable_bounds':{s:bounds([c['response_pair'] for c in mixed],s) for s in SIGNS},
        'controls':aggregate(controls),
        'by_pattern':{p:aggregate(where(cases,'pattern',p)) for p in SIGNS},
        'by_order':{q:aggregate(where(cases,'first',q)) for q in ('any','both')},
        'mixed_by_order':{q:aggregate(where(mixed,'first',q)) for q in ('any','both')},
        'by_family':{f:aggregate(where(cases,'family',f)) for f in sorted({c['family'] for c in cases})},
        'transcription':{'maps_returned':sum(bool(c['reported_labels']) for c in cases),
                         'exact':sum(c['exact_labels'] for c in cases),
                         'matching_fields':sum(c['label_hits'] for c in cases),
                         'accepted_maps_by_field_hits':counts(c['label_hits'] for c in cases if c['reported_labels']),
                         'mixed_id_swaps':sum(c['reported_labels']==c['pattern'][::-1] for c in mixed)},
        'stages':{},'behavioral_maps':{}, 'omissions':[], 'paid_api_usd':0,
    }
    for s,raw in receipts.items():
        summary['stages'][s]=dict(issued=len(raw), statuses=counts(r['status'] for r in raw),
            finish=counts(str(r.get('usage',{}).get('done_reason') or 'unavailable') for r in raw),
            totals={k:sum(r.get('usage',{}).get(k) or 0 for r in raw) for k in
                    ('prompt_eval_count','eval_count','total_duration','load_duration','eval_duration')})
    for name,rule in MAPS.items():
        matched=[c for c in cases if c['response_pair']==rule(c['pattern'])]
        summary['behavioral_maps'][name]=dict(full_matches=len(matched),mixed_matches=sum(c in mixed for c in matched),
                 full_layouts=sorted(f for f in summary['by_family'] if len(where(matched,'family',f))==4),
                 complete_mismatches=[c['record'] for c in cases if c['complete'] and c not in matched])
    summary['omissions']=[dict(record=c['record'],labels=c['labels_status'],any=c['any_status'],both=c['both_status'])
                          for c in cases if not c['complete']]
    dest=HERE/'results';dest.mkdir(exist_ok=True)
    with (dest/'cases.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(cases[0]))
        writer.writeheader();writer.writerows(cases)
    save(dest/'summary.json',summary)
    return summary


if __name__=='__main__':
    print(analyze()['mixed'])
