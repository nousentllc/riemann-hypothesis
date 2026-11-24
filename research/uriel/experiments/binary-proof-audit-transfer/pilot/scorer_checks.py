"""Exhaust all lookup/certificate possibilities on the frozen finite worlds."""
from collections import Counter
from itertools import combinations
from domain import build_data, oracle, label, remaining, score_answer, score_session

def exemplar(row, survivors):
    t=label(row,survivors)
    if t!='U': return dict(verdict=t,certificate=survivors)
    left=survivors[0]
    right=next(i for i in survivors if row['states'][i]['answer']!=row['states'][left]['answer'])
    return dict(verdict=t,certificate=[left,right])

def run():
    dataset=build_data(); counts=Counter()
    for part, rows in dataset.items():
        for rid, row in rows.items():
            target=oracle(row)
            expected_settled = target['initial']!='U'
            actions=[v for v in ['NONE',*row['menu']]]
            pass_count=0
            for item in actions:
                after=remaining(row,item)
                first={**exemplar(row,remaining(row)),'lookup':item}
                final=exemplar(row,after)
                receipt={'first':{'answer':first},'second':{'answer':final}}
                got=score_session(row,receipt)
                assert got['pass_case']==(final['verdict']==target['target'])
                pass_count+=int(got['pass_case'])
                assert got['unsupported']==0
                for size in range(0,len(row['states'])+1):
                    for picked in combinations(row['states'],size):
                        for verdict in ('Y','N','U'):
                            if verdict=='U':
                                valid=(len(picked)==2 and set(picked)<=set(after) and len({row['states'][s]['answer'] for s in picked})==2)
                            else:
                                valid=(set(picked)==set(after) and all(row['states'][s]['answer']==(verdict=='Y') for s in after))
                            observed=score_answer(row,{'verdict':verdict,'certificate':list(picked)},after)
                            assert observed['certified']==valid,(rid,item,verdict,picked)
                            counts[part]+=1
                duplicate=after[0]
                assert not score_answer(row,dict(verdict=final['verdict'],certificate=[duplicate,duplicate]),after)['certified']
            assert pass_count>0
            assert not score_session(row,{'first':{'answer':None}})['pass_case']
    print('All exhaustive certificate tests passed:',dict(counts))

if __name__=='__main__': run()
