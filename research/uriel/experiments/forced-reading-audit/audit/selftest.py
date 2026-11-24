"""Fault-inject fabricated responses in a temporary copy of the frozen inputs, with no model calls."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

import check as audit


def reject(thunk, contains):
    try:
        thunk()
    except ValueError as exc:
        if contains not in str(exc):
            raise
    else:
        raise AssertionError(f'Failed to detect injected fault for {contains}.')


def write(p,obj):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')


def main():
    original=audit.ROOT
    with TemporaryDirectory() as tmp:
        root=Path(tmp)
        freeze=audit.read(original/'pilot'/'freeze.json')
        for path in [*freeze['sha256'],'pilot/freeze.json']:
            dest=root/path; dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(original/path,dest)
        sys.path.insert(0,str(root/'pilot'))
        import instrument
        cases,families,jobs,_=audit.inspect_pre(root)
        answers={}
        for c in cases.values():
            for arm in audit.ARMS:
                ids=sorted(c['live'])
                # All filtered families certify, some full sessions claim too much or repeat IDs.
                doc={'verdict':c['target'],'certificate':ids}
                if arm=='full' and c['kind']=='decisive':
                    idx=int(c['rid'].rsplit('-',1)[1]) % 3
                    if idx==0:
                        doc={'verdict':'U','certificate':ids}
                    elif idx==1:
                        doc={'verdict':c['target'],'certificate':[ids[0],ids[0]]}
                answers[c['texts'][arm]]=doc

        captured=[]
        def fake_local(url,payload):
            if url!='/api/chat':
                raise ValueError('Unexpected simulated endpoint.')
            prompt=payload['messages'][1]['content']
            captured.append(payload)
            return {'model':audit.MODEL,'done':True,'done_reason':'stop',
                    'message':{'content':json.dumps(answers[prompt])},'prompt_eval_count':12,'eval_count':7,
                    'total_duration':100,'load_duration':1,'eval_duration':90}
        instrument.local=fake_local
        system=(root/'pilot'/'method.txt').read_text().strip()
        indices={rid:i for i,rid in enumerate(sorted(cases))}
        for j in jobs:
            rid,arm=j['record'],j['arm']; c=cases[rid]
            messages=[{'role':'system','content':system},{'role':'user','content':c['texts'][arm]}]
            dest=root/'pilot'/'observed'/f'{rid}_{arm}'/'response.json'
            instrument.stage(dest,messages,c['params'],'gptoss',audit.SEED+indices[rid],False)
        assert len(captured)==36
        subprocess.run([sys.executable,'-B',str(root/'pilot'/'analyze.py')],check=True,stdout=subprocess.DEVNULL)
        report=audit.inspect_post(root,cases,families,jobs)
        assert report['request_hashes_verified']==36 and report['totals']['filtered']['certified']==18
        rid=next(iter(cases));c=cases[rid]
        prompt=root/'pilot'/'prompts'/f'{rid}.filtered.txt'
        before=prompt.read_bytes()
        # The checksum gate alone could bless a corrupted presentation after an incorrect re-freeze.
        idx=before.index(b'ID stu target_current initial ')
        a,b=before[:idx],before[idx:]
        after=b.split(b'\n')
        after[1],after[2]=after[2],after[1]
        prompt.write_bytes(a+b'\n'.join(after))
        reject(lambda:audit.materialize_pair(root,rid,c['params']),'six rows deleted')
        prompt.write_bytes(before)
        json_path=root/'pilot'/'observed'/f'{rid}_filtered'/'response.json'
        backup=json_path.read_bytes()
        receipt=audit.read(json_path)
        # Rebuild a request with a filtered response grammar. Other configuration and raw output stay fixed.
        receipt['request_sha256']=audit.request_hash(system,c['texts']['filtered'],sorted(c['live']),audit.SEED+indices[rid])
        write(json_path,receipt)
        reject(lambda:audit.inspect_post(root,cases,families,jobs),'request text, enumerated IDs')
        json_path.write_bytes(backup)
        summ_path=root/'pilot'/'results'/'summary.json'
        doc=audit.read(summ_path);doc['primary']['filtered_only']+=1
        write(summ_path,doc)
        reject(lambda:audit.inspect_post(root,cases,families,jobs),'family pair value')
    print('Simulated 36 calls; verified all request hashes, production scoring, and three injected faults. No inference.')


if __name__=='__main__':
    main()
