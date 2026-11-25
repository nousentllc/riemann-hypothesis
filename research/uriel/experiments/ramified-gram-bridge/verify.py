"""Offline numerical and evidence-integrity checks. See verification/replay.py for Lean."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
def read(name):
    return json.loads((ROOT/name).read_text())
def run():
    for script,saved in [('local/chart_experiment','local/chart_results'),('global/controls','global/controls'),
                         ('dyadic/experiment','dyadic/results'),('synthesis/gaussian_product','synthesis/gaussian_product')]:
        out=subprocess.check_output([sys.executable,'-B',ROOT/(script+'.py')],cwd=ROOT,text=True)
        assert json.loads(out)==read(saved+'.json'),script
    ramified = subprocess.check_output([sys.executable,'-B',ROOT/'literature/ramified_probe.py'],cwd=ROOT,text=True)
    assert json.loads(ramified)==read('literature/ramified_results.json')
    spectra=subprocess.check_output([sys.executable,'-B',ROOT/'bridge/characters.py'],text=True)
    assert json.loads(spectra)==read('bridge/characters.json')
    neighbors=subprocess.check_output([sys.executable,'-B',ROOT/'bridge/neighbors.py'],text=True)
    assert json.loads(neighbors)==read('bridge/neighbors.json')
    subprocess.run([sys.executable,'-B',ROOT/'bridge/RamBaseCertificate.py'],check=True)
    inv=read('study_imports.json')
    original=read('original_imports.json')
    receipt=read('verification/receipt.json')
    assert set(receipt['modules'])==set(inv['modules'])
    for m,row in receipt['modules'].items():
        assert row['lean_exit']==row['leanchecker_exit']==0,m
        source=ROOT/inv['modules'][m]['file']
        assert hashlib.sha256(source.read_bytes()).hexdigest()==row['source'],m
        for ds in row['axiom_queries'].values():
            assert set(ds)<={'Classical.choice','Quot.sound','propext'},m
    required={'OptimalSupport':'OptimalSupport.positive_iff_multiple','UncappedGrowth':'UncappedGrowth.all_multiples',
              'OriginalFloor':'OriginalFloor.punctured_floor','GaussianSharp':'DyadicWave.sharp_floor',
              'SquareDepth':'DyadicWave.with_unit','GaussianDilates':'DyadicWave.realized_all'}
    for m,decl in required.items():assert decl in receipt['modules'][m]['axiom_queries'],decl
    dyadic=read('dyadic/receipt.json')
    assert any("'DyadicWave.fiber_mass' depends on axioms: [propext, Classical.choice, Quot.sound]" in v for v in dyadic.values() if isinstance(v,str))
    assert receipt['modules']['UncappedAudit']['dependency_audit']==(ROOT/'verification/dependencies.txt').read_text().strip()
    for name,h in read('verification/pinned_excerpts.json').items():
        b=(ROOT/'pinned'/name).read_bytes()
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h,name
    assert 'RamPlaceEndpoint.original' in receipt['modules']['RamPlaceEndpoint']['axiom_queries']
    assert 'RamPlaceEndpoint.realized' in receipt['modules']['RamPlaceEndpoint']['axiom_queries']
    assert receipt['modules']['RamDependencyAudit']['dependency_audit']==(ROOT/'verification/ramified_dependencies.txt').read_text().strip()
    assert receipt['negative_control']['lean_exit']!=0 and receipt['negative_control']['changed_numerator_by']==1
    assert receipt['original_objects']==receipt['verified_source_blobs']==len(original)
    print(f'The ramified census, exact-character check, and inherited controls reproduced. {len(inv["modules"])} module source digests and axiom receipts match. {len(original)} original dependencies inventoried.')
if __name__=='__main__':run()
