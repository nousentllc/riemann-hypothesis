"""Exhaustive logical controls and offline replay using each submitted label map as written."""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]

def fold(labels):
    return ('N','U','Y')[sum(v=='Y' for v in labels)]

def controls():
    counts=Counter()
    for truth in product('YN',repeat=2):
        for written in product('YN',repeat=2):
            errors=sum(a!=b for a,b in zip(truth,written))
            same=fold(truth)==fold(written)
            assert same == (errors==0 or errors==2 and truth[0]!=truth[1])
            assert fold(written)==fold(written[::-1])
            for final in 'YNU':
                counts[(errors, same, final==fold(truth), final==fold(written))]+=1
                if truth==written:
                    assert (final==fold(truth))==(final==fold(written))
    assert sum(counts.values())==48
    return {str(k):v for k,v in sorted(counts.items())}

def replay():
    truth_table=controls()
    data=json.loads((ROOT/'audit/post.json').read_bytes())['cases']; examples={}; flow=Counter()
    for key,r in data.items():
        if not key.endswith('_label_first'):continue
        actual=r['committed_labels']; truth=r['public_labels']
        output_ok=r['warranted']
        predicted=fold(actual.values()) if actual is not None else None
        replay_ok=predicted==fold(truth.values())
        group=('both' if output_ok and replay_ok else 'replay_only' if replay_ok else 'model_only' if output_ok else 'neither')
        flow[group]+=1; examples[key.rsplit('_label_first',1)[0]]=dict(model=r['verdict'],replay=predicted,truth=r['truth'],cell=group)
    matrix={}
    for rid in examples:
        status=[]
        for arm in ('direct','label_first'):
            c=data[rid+'_'+arm]
            status.append('warranted' if c['warranted'] else 'missing' if c['verdict'] is None else 'wrong')
        matrix.setdefault('/'.join(status),[]).append(rid)
    out=dict(controls=truth_table,flows=flow,records=examples,paired_delivery=matrix)
    p=ROOT/'audit/composition.json'
    text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if '--verify' in sys.argv: assert p.read_text()==text
    else: p.write_text(text)
    print(dict(flow))

if __name__=='__main__':
    if '--controls' in sys.argv:print('All',sum(controls().values()),'binary-report/verdict triples passed.')
    else:replay()
