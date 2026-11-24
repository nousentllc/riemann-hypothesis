"""Synthetic bounds checks. Never opens study observations or score tables."""
from collections import Counter
from itertools import product
from bounds import OUTCOMES,AXES,analyze


def synthetic(n,full=(0,0),filtered=(0,0)):
    rows=[]
    for i in range(n):
        for arm,default in [('full',full),('filtered',filtered)]:
            for j in range(3):
                rows.append(dict(family=str(i),record=f'{i}-{j}',kind='decisive' if j<2 else 'ambiguous',arm=arm,
                                 ids=bool(default[0]),certified=bool(default[1]),status='ok',verdict='Y'))
    return rows


def erase(row):
    row.update(ids=False,certified=False,status='error',verdict='')


def brute_force(rows):
    hist=Counter()
    unknown=[i for i,r in enumerate(rows) if r['status']!='ok']
    for values in product(OUTCOMES,repeat=len(unknown)):
        view=[(int(r['ids']),int(r['certified'])) for r in rows]
        for i,v in zip(unknown,values):view[i]=v
        score={}
        for arm in ('full','filtered'):
            arm_rows=[(r,x) for r,x in zip(rows,view) if r['arm']==arm]
            dec=[(r,x) for r,x in arm_rows if r['kind']=='decisive']
            complete=sum(1 for f in {r['family'] for r,_ in dec} if all(x[1] for r,x in dec if r['family']==f))
            score[arm]=(complete,sum(x[0] for r,x in dec),sum(x[1] for r,x in arm_rows if r['kind']=='ambiguous'))
        hist[tuple(b-a for a,b in zip(score['full'],score['filtered']))]+=1
    return hist


def verify(rows):
    res=analyze(rows); ground=brute_force(rows)
    assert res['possible_distinct_endpoint_triples']==len(ground)
    assert res['possible_endpoint_class_assignments']==sum(ground.values())
    assert res['sharp_ranges']=={key:[min(x[i] for x in ground),max(x[i] for x in ground)] for i,key in enumerate(AXES)}
    count=sum(v for (families,ids,control),v in ground.items() if families>=2 and ids>=2 and control>=0)
    assert res['class_assignments_passing_gate']==count
    return res


def test():
    a=synthetic(2,(0,0),(1,1))
    got=verify(a); assert got['attainable_gate_outcomes']==[True]
    b=synthetic(2);erase(b[1]);erase(b[5])
    got=verify(b);assert got['attainable_gate_outcomes']==[False]
    c=synthetic(2,(0,0),(1,1));erase(c[3]);erase(c[10])
    got=verify(c);assert got['registered_gate'] is False and got['attainable_gate_outcomes']==[False,True]
    d=synthetic(2,(0,0),(1,1));d[5].update(ids=False,certified=False);d[11].update(ids=False,certified=False)
    erase(d[2]); got=verify(d);assert got['registered_gate'] and got['can_change_registered_gate']
    all_missing=synthetic(6)
    for r in all_missing:erase(r)
    got=analyze(all_missing)
    assert got['possible_endpoint_class_assignments']==3**36
    assert list(got['sharp_ranges'].values())==[[-6,6],[-12,12],[-6,6]]
    assert got['attainable_gate_outcomes']==[False,True]
    print('Four synthetic paired panels matched direct enumeration; all-missing six-layout bounds passed.')


if __name__=='__main__':test()
