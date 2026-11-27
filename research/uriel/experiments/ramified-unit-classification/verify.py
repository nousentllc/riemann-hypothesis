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
    observed_dilates=subprocess.check_output([sys.executable,'-B',ROOT/'dilates/experiment.py'],text=True)
    assert json.loads(observed_dilates)==read('dilates/results.json')
    companion=subprocess.check_output([sys.executable,'-B',ROOT/'dilates/companion_counts.py'],text=True)
    assert json.loads(companion)==read('dilates/companion_counts.json')
    unit_result=subprocess.check_output([sys.executable,'-B',ROOT/'dilates/unit_experiment.py'],text=True)
    assert json.loads(unit_result)==read('dilates/unit_results.json')
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
    for claim in ('original','realized','sixteen','counts','powers'):
        assert 'RamDilate.'+claim in receipt['modules']['DilateEndpoint']['axiom_queries']
    for module,claim in (
            ('DilateSixteen','RamDilate.contact_sixteen'),
            ('DilateCompanion','RamDilate.companion_count'),
            ('DilateOddCellHaar','RamDilate.OddCell.last_odd_haar'),
            ('DilateNear','RamDilate.near_count'),
            ('DilateStableOddAll','RamDilate.StableOdd.sharp_stabilization')):
        assert claim in receipt['modules'][module]['axiom_queries'],claim
    assert 'RamDilate.last_shortfall' in receipt['modules']['DilateBoundary']['axiom_queries']
    assert receipt['modules']['DilateAudit']['dependency_audit']==(ROOT/'verification/dilate_dependencies.txt').read_text().strip()
    control=receipt['dilate_negative_control']
    assert control['lean_exit']!=0 and control['changed_numerator_by']==1 and control['expected_count']==65537*2**35
    companion_declarations = {
        'CompanionObstruction': ['RamDilate.Companion.no_companion_unit'],
        'CompanionLow': ['RamDilate.Companion.low3_twice'],
        'CompanionPrimitive': ['RamDilate.CompanionPrimitive.primitive_later'],
        'CompanionCounts': ['RamDilate.Companion.band'],
        'CompanionCells': ['RamDilate.Companion.all_late', 'RamDilate.Companion.predecessor',
                           'RamDilate.Companion.sharp_stabilization'],
        'CompanionEndpoint': ['CompanionTransport.original', 'CompanionTransport.realized'],
    }
    for module, declarations in companion_declarations.items():
        assert set(declarations) <= receipt['modules'][module]['axiom_queries'].keys(), module
    wrong_sign = receipt['companion_wrong_sign']
    assert wrong_sign['lean_exit'] != 0 and wrong_sign['rejected_square_count'] == 2155872256
    assert wrong_sign['companion_count'] == 2139095040
    unit_declarations = {
        'UnitResidue': ['RamDilate.UnitClass.decomposition'],
        'UnitLow': ['RamDilate.UnitClass.low2_one', 'RamDilate.UnitClass.low3_one',
                    'RamDilate.UnitClass.low3_two'],
        'UnitCounts': ['RamDilate.UnitClass.same_as_square', 'RamDilate.UnitClass.count_positive'],
        'UnitCells': ['RamDilate.UnitClass.band_count', 'RamDilate.UnitClass.all_late'],
        'UnitDepth': ['RamDilate.UnitClass.predecessor', 'RamDilate.UnitClass.sharp_stabilization'],
        'UnitEndpoint': ['UnitTransport.original', 'UnitTransport.valuation_shell',
                         'UnitTransport.valuation_exponent', 'UnitTransport.exact_range_at_exponent',
                         'UnitTransport.values_distinct', 'UnitTransport.realized'],
    }
    for module, declarations in unit_declarations.items():
        assert set(declarations) <= receipt['modules'][module]['axiom_queries'].keys(), module
    nonsquare = receipt['positive_nonsquare_control']
    assert nonsquare['lean_exit'] != 0 and nonsquare['coefficient_modulus'] == 4
    assert nonsquare['unit_coefficients'] == [1, 2]
    paper=read('verification/paper.json')
    for name,key in [('Ramified_Gram_Fiber_Mass_Classes.tex','source_sha256'),('Ramified_Gram_Fiber_Mass_Classes.pdf','pdf_sha256'),
                     ('verification/receipt.json','lean_receipt_sha256')]:
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==paper[key],name
    assert paper['body_pages']>=30 and paper['independent_standalone_build_byte_identical']
    assert receipt['original_objects']==receipt['verified_source_blobs']==len(original)
    print(f'The all-address shell counts, inherited census and independent controls reproduced. {len(inv["modules"])} module source digests and axiom receipts match. {len(original)} original dependencies inventoried.')
if __name__=='__main__':run()
