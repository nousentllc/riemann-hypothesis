"""Validate the evidence package offline. Full independent replay uses verification/replay.py."""
import hashlib
import json
from pathlib import Path
from graphlib import TopologicalSorter

ROOT=Path(__file__).resolve().parent


def git_blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def verify():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    imports=json.loads((ROOT/'original_imports.json').read_text())
    receipt=json.loads((ROOT/'verification/receipt.json').read_text())
    assert receipt['original']==manifest['original_commit']
    assert len(imports)==receipt['original_dependency_count']==1863
    assert sum(r['official_olean_sha256']==r['used_olean_sha256'] for r in imports.values())==receipt['mit_object_matches']==1017
    assert set(TopologicalSorter({n:r['imports'] for n,r in imports.items()}).static_order())==set(imports)
    for f,r in manifest['anchors'].items():assert git_blob((ROOT/'anchors'/f).read_bytes())==r['blob']
    for n,h in manifest['inherited'].items():assert git_blob((ROOT/'inherited'/(n+'.lean')).read_bytes())==h
    contents=[]
    for row in receipt['rebuilt']:
        name=row['module']
        f=name.split('.')[-1]+'.lean'
        matches=[p for p in [ROOT/'anchors'/f,ROOT/'inherited'/f,ROOT/'verification'/f] if p.is_file()]
        assert len(matches)==1 and hashlib.sha256(matches[0].read_bytes()).hexdigest()==row['source_sha256']
        assert row['kernel']=='replaying '+name
        contents.extend(row['findings'])
    for name in ['ProgressionGrowth.progression_growth','ProgressionEndpoint.sw_one_via_progression',
                 'CappedGrowth.bounded_order_growth','GrowthConsumer.forces_iff_relativeGrowth',
                 'GrowthConsumer.sw_one_of_growth','FourSquareControl.no_uniform_lower']:
        assert f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in contents
    assert len([l for l in contents if l.startswith('AUDIT ')])==4
    broad=(ROOT/'verification/import_replay.txt').read_text()
    assert '1863 modules' in broad and 'Kernel accepted and located' in broad
    assert (ROOT/'Parallel_Growth.pdf').read_bytes().startswith(b'%PDF')
    assert len(list(ROOT.rglob('*.tex')))==len(list(ROOT.rglob('*.pdf')))==1
    print('Verified the original dependencies, proof sources, kernel receipts, route controls and manuscript pair.')


if __name__=='__main__':
    verify()
