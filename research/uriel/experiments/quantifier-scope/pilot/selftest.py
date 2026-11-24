"""Exhaustive score controls, independent of model observations."""
from itertools import product
from analyze import MAPS, SIGNS, aggregate, bounds, classify
from instrument import ROOT, parse_answer
from run import read


def test():
    records = read(ROOT/'circuits/records.json')
    assert dict((p,MAPS['scope'](p)) for p in SIGNS)=={'YY':'YY','YN':'YN','NY':'YN','NN':'NN'}
    for rid,row in records.items():
        ids=row['survivors']; pattern=''.join('Y' if row['states'][i]['answer'] else 'N' for i in ids)
        for report in SIGNS:
            for a,b in product('YN-',repeat=2):
                receipts={'labels':dict(status='ok',answer=dict(zip(ids,report)))}
                for q,sym in [('any',a),('both',b)]:
                    receipts[q]=dict(status='invalid',answer=None) if sym=='-' else dict(status='ok',answer={'answer':sym})
                c=classify({'record':rid,'query_order':['any','both']},row,receipts)
                assert c['joint_correct']==(a+b==MAPS['scope'](pattern))
                assert c['complete']==('-' not in (a,b))
                assert c['exact_labels']==(pattern==report)
                for i,q in enumerate(('any','both')):
                    val=(a,b)[i]
                    assert c[q+'_coherent']==('' if val=='-' else int(val==MAPS['scope'](report)[i]))
                for target in SIGNS:
                    fills=[x+y for x,y in product('YN',repeat=2) if (a=='-' or a==x) and (b=='-' or b==y)]
                    assert bounds([a+b],target)==[int(all(z==target for z in fills)),int(target in fills)]
        c=classify({'record':rid,'query_order':['both','any']},row,{'labels':{'status':'error','answer':None}})
        assert c['response_pair']=='--' and c['any_status']=='gated' and not c['exact_labels']
        assert aggregate([c])['partials']=={'--':1}
    assert parse_answer('{"answer":"N","answer":"Y"}',row,'any') is None
    print('All synthetic scorer and missing-outcome controls passed.')


if __name__=='__main__':
    test()
