"""Exercise missing replies, impossible certificates, and tamper detection on synthetic receipts."""
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]


def load(path, name):
    spec = spec_from_file_location(name,path)
    mod = module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    manifest = json.loads((ROOT/'pilot/freeze.json').read_bytes())
    with TemporaryDirectory() as td:
        root = Path(td)
        for filename in [*manifest['sha256'],'pilot/freeze.json','audit/check.py']:
            target = root/filename
            target.parent.mkdir(exist_ok=True,parents=True)
            shutil.copyfile(ROOT/filename,target)
        audit = load(root/'audit/check.py','independent_simulation')
        engine = load(root/'pilot/instrument.py','original_simulation')
        rows,cases,jobs,_ = audit.inspect_panel()
        for job in jobs:
            rid,arm = job['record'],job['arm']
            c,row = cases[rid],rows[rid]
            key = rid+'_'+arm
            dest = root/'pilot/observed'/key
            seed = 2026112429+int(rid.split('-')[-1])
            state_answer = lambda s: row['states'][s]['answer']
            def answer(pool):
                yes = sorted(i for i in pool if state_answer(i))
                no = sorted(i for i in pool if not state_answer(i))
                cert = [yes[0],no[0]] if yes and no else sorted(pool)
                return dict(verdict='U' if yes and no else ('Y' if yes else 'N'),certificate=cert)
            a = answer(c['live'])
            if arm=='labeled' and c['kind']=='lookup':
                a['lookup'] = c['certain'][0]
            elif arm=='raw' and c['kind']=='lookup':
                a['lookup'] = next(m for m in c['menu'] if m not in c['certain'])
            else:
                a['lookup'] = 'NONE'
            if c['kind']=='settled' and arm=='raw':
                a['certificate'] += [a['certificate'][0]]
            session = dict(record=rid,arm=arm)
            messages = [dict(role='system',content=(root/'pilot/method.txt').read_text().strip()),
                        dict(role='user',content=(root/'pilot/prompts'/(rid+'.'+arm+'.txt')).read_text())]
            for st in ('first','second'):
                missing = arm=='labeled' and c['kind']=='ambiguous'
                def reply(path,payload):
                    if path!='/api/chat':
                        raise RuntimeError('Unexpected simulation route.')
                    return dict(model='gpt-oss:20b',message={'content':'' if missing else json.dumps(a)},
                                done_reason='length' if missing else 'stop',done=True,prompt_eval_count=1,eval_count=2)
                engine.local = reply
                g = engine.stage(dest/(st+'.json'),messages,row,'gptoss',seed if st=='first' else seed+1000,st=='first')
                session[st] = g
                if st=='second' or missing or a.get('lookup')=='NONE':
                    break
                item = a['lookup']
                value = row['states'][row['actual']]['obs'][item]
                session['observation'] = dict(item=item,value=value)
                messages += [dict(role='assistant',content=g['content']),dict(role='user',content=(
                    f'Lookup {item} returns: {value}. Give the final verdict and the certificate for the '
                    'evidence now available. Return only verdict and certificate.'))]
                a = answer(c['actual_cells'][item])
            engine.save(dest/'session.json',session)
        subprocess.run([sys.executable,'-B',root/'pilot/analyze.py'],check=True,stdout=subprocess.DEVNULL)
        def run():
            r,c,j,pre = audit.inspect_panel()
            return audit.inspect_results(r,c,j,pre)
        scores = run()
        assert scores['totals']['labeled']['productive']==6 and scores['totals']['raw']['productive']==0
        assert scores['totals']['labeled']['invalid_calls']==3 and scores['representation_follow_up_gate']
        tested = []
        def must_reject(path,replacement,label):
            original = path.read_bytes()
            path.write_bytes(replacement)
            try:
                run()
            except ValueError:
                tested.append(label)
            else:
                raise RuntimeError('Audit did not detect '+label)
            finally:
                path.write_bytes(original)
        prompt = root/'pilot/prompts/circuit-00.labeled.txt'
        # Rehash the altered file to specifically test the prompt parser, apart from the hash gate.
        s = prompt.read_text()
        h = s.index('target_current_above_threshold')
        start = s.index('\n',h)+1
        end = s.index('\n',start)
        s = s[:end-1]+('Y' if s[end-1]=='N' else 'N')+s[end:]
        frozen = root/'pilot/freeze.json'
        original_freeze = frozen.read_bytes()
        m = json.loads(original_freeze)
        m['sha256']['pilot/prompts/circuit-00.labeled.txt'] = sha256(s.encode()).hexdigest()
        frozen.write_text(json.dumps(m))
        must_reject(prompt,s.encode(),'miscomputed displayed threshold bit after matching hash')
        frozen.write_bytes(original_freeze)
        receipt = root/'pilot/observed/circuit-00_labeled/session.json'
        v = json.loads(receipt.read_bytes())
        v['observation']['value'] = 'L' if v['observation']['value']=='H' else 'H'
        must_reject(receipt,json.dumps(v).encode(),'reversed returned meter value')
        official = root/'pilot/results/summary.json'
        v = json.loads(official.read_bytes())
        v['totals']['raw']['certified'] += 1
        must_reject(official,json.dumps(v).encode(),'inflated official certificate count')
        print(json.dumps(dict(fictitious_sessions=24,verified_requests=scores['request_hashes_checked'],
                              detected=tested,real_model_calls=0),indent=2))


if __name__=='__main__':
    main()
