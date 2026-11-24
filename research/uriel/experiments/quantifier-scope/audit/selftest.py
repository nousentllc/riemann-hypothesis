"""Challenge the independent audit using invented response histories; there are no network calls."""
import json
from datetime import datetime, timedelta, timezone
from pathlib import Path
from shutil import copytree
from tempfile import TemporaryDirectory

from check import ROOT, QUESTIONS, SIGS, SYSTEM, bounds, child, fit, identify_conflicts, payload, post, pre, read, require, selftest, sha

REG={'committed_at':'2025-01-01T00:00:00+00:00','commit':'synthetic'}


def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2)+'\n')


def synthetic(root,data):
    copytree(ROOT/'pilot/prompts',root/'pilot/prompts')
    jobs=read(ROOT/'pilot/order.json')
    save(root/'pilot/order.json',jobs)
    time=datetime(2027,1,1,tzinfo=timezone.utc)
    synthetic_cases={}
    omitted=next(rid for rid,d in data.items() if d['pattern']=='YN')
    partial=next(rid for rid,d in data.items() if d['pattern']=='NY')
    swapped=next(rid for rid,d in data.items() if d['pattern']=='YN' and rid!=omitted)
    for ix,job in enumerate(jobs):
        rid=job['record']
        d=data[rid]
        truth=d['truth'].copy()
        if rid==swapped:
            truth=dict(zip(truth,reversed(list(truth.values()))))
        seed=d['seed']
        msgs=[dict(role='system',content=SYSTEM),dict(role='user',content=(root/'pilot/prompts'/f'{rid}.labels.txt').read_text())]
        checkpoint=json.dumps(truth,indent=2) if rid!=omitted else ''
        seq=[('labels',payload(msgs,seed+1000,d['truth']),checkpoint)]
        assigned=SIGS[ix%4]
        if rid!=omitted:
            for q in d['order']:
                partial_fail=rid==partial and q==d['order'][0]
                content='' if partial_fail else json.dumps({'answer':assigned[list(QUESTIONS).index(q)]})
                seq.append((q,child(msgs,checkpoint,q,seed),content))
        for stage,req,content in seq:
            folder=root/'pilot/observed'/rid/stage
            save(folder/'request.json',req)
            started=dict(started=time.isoformat(),request_sha256=sha(req))
            save(folder/'response.started',started)
            time+=timedelta(seconds=1)
            valid=bool(content)
            save(folder/'response.json',dict(**started,ended=time.isoformat(),status='ok' if valid else 'invalid',
                answer=json.loads(content) if valid else None,content=content,usage={'done_reason':'stop' if valid else 'length'}))
        synthetic_cases[rid]=assigned
    return omitted,partial,swapped,synthetic_cases


def challenge(root, rid,stage,data,change,match):
    folder=root/'pilot/observed'/rid/stage
    files=('request.json','response.json','response.started')
    original={p:(folder/p).read_bytes() for p in files}
    try:
        req=read(folder/files[0])
        change(req)
        save(folder/files[0],req)
        for p in files[1:]:
            rec=read(folder/p)
            rec['request_sha256']=sha(req)
            save(folder/p,rec)
        try:
            post(root,data,REG)
        except ValueError as err:
            require(match in str(err),'Unexpected reason: '+str(err))
        else:
            raise ValueError('Mutated history passed')
    finally:
        for p,b in original.items():
            (folder/p).write_bytes(b)


def main():
    selftest()
    data=pre(ROOT)
    with TemporaryDirectory() as directory:
        root=Path(directory)
        missing,partial,swapped,assigned=synthetic(root,data)
        report=post(root,data,REG)
        cases=report['cases']
        require(report['verified_requests']==70,'Gate must suppress exactly two children')
        require(cases[missing]['possible_signatures']==list(SIGS),'Both answers absent')
        require(len(cases[partial]['possible_signatures'])==2 and assigned[partial] in cases[partial]['possible_signatures'],'Partial must retain exactly one observed bit')
        require(cases[partial]['status'][data[partial]['order'][1]]=='ok','Second sibling did not survive first branch failure')
        require(cases[swapped]['labels_hits']==0 and not cases[swapped]['exact_checkpoint'] and cases[swapped]['complete'],'Mixed ID reversal must count as transcription failure')
        clean=next(i for i in data if i not in {missing,partial,swapped})
        first,last=data[clean]['order']
        content_dir=root/'pilot/observed'/clean
        contaminant=read(content_dir/first/'response.json')['content']
        def changed_report(req):
            req['messages'][-2]['content']+=' '
        def sibling_history(req):
            req['messages'][-1:-1]=[{'role':'user','content':QUESTIONS[first]},{'role':'assistant','content':contaminant}]
        def seed_drift(req):
            req['options']['seed']+=1
        def grammar_drift(req):
            req['format']['properties']['answer']['enum']=['Y']
        for intervention in (changed_report,sibling_history,seed_drift,grammar_drift):
            challenge(root,clean,last,data,intervention,'Unexpected request history, grammar or seed')
        orphan=root/'pilot/observed'/missing/'both'
        orphan.mkdir()
        try:
            post(root,data,REG)
        except ValueError as e:
            require('Invalid checkpoint leaked to children' in str(e),str(e))
        else:
            raise ValueError('Orphaned child passed')
        orphan.rmdir()
        require(post(root,data,REG)==report,'Fixture restoration failed')
    conflict_controls={
        'swapped':dict(reported_pattern='NY',expected='YN',exact_checkpoint=False,any='Y',both='N'),
        'phys':dict(reported_pattern='NN',expected='YY',exact_checkpoint=False,any='Y',both='N'),
        'missing-branch':dict(reported_pattern='YY',expected='YN',exact_checkpoint=False,any='Y',both=None),
        'missing-map':dict(reported_pattern=None,expected='YN',exact_checkpoint=False,any=None,both=None)}
    c=identify_conflicts(conflict_controls)
    require(c['records']['swapped']['discriminating_branches']=={} and c['types']['inaccurate_but_permutation_equivalent']==1,'A map reversal preserves quantifier truth')
    require(c['by_question']['any']==dict(different_references=1,followed_physical=1,followed_report=0,missing=0),'Distinguishable existential branch')
    require(c['by_question']['both']==dict(different_references=2,followed_physical=0,followed_report=1,missing=1),'Distinguishable universal branch')
    mixed=('NY','YN')
    require(all(fit(p,'scope')==fit(p,'wording_only')=='YN' for p in mixed),'Mixed alias control')
    require(all(fit(p,'or_on_both')==fit(p,'always_yes')=='YY' for p in mixed),'Mixed equal-yes alias control')
    require(fit('NN','or_on_both')=='NN' and fit('NN','always_yes')=='YY','All-negative discrimination control')
    require(fit('YY','scope')=='YY' and fit('NN','scope')=='NN' and all(fit(p,'wording_only')=='YN' for p in ('YY','NN')),'Homogeneous discrimination control')
    require(fit('NY','first_row_twice')==fit('YN','second_row_twice')=='NN','Position reversal control')
    print('Synthetic audit passed: 36 missing-data cells, role/seed/schema substitutions, gated and partial branches, ID reversal, and paired truth-table controls.')


if __name__=='__main__':
    main()
