"""Check module identities and replay evidence without a Lean installation."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def git_blob(data):
    header = b'blob ' + str(len(data)).encode() + b'\0'
    return hashlib.sha1(header + data).hexdigest()


def audit():
    manifest = json.loads((ROOT/'manifest.json').read_text())
    receipt = json.loads((ROOT/'verification/receipt.json').read_text())
    results = receipt['kernel_replay']
    assert len(results) == len(manifest['modules']) == 64
    assert manifest['mathlib'] == receipt['mathlib'] and manifest['lean'] in receipt['toolchain']
    names = set()
    for row, entry in zip(manifest['modules'], results):
        data = (ROOT/row['path']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row['sha256'] == entry['source_sha256']
        if row['kind'] == 'pinned':
            assert git_blob(data) == row['git_blob']
        assert names.issuperset(row['imports'])
        name = row['module']
        assert name not in names and entry['module'] == name and entry['kernel'] == 'replaying '+name
        names.add(name)
    assert {p.stem for p in (ROOT/'verification').glob('*.lean')} == {
        row['module'] for row in manifest['modules'] if row['kind'] == 'study'}
    for row in manifest['references']:
        assert git_blob((ROOT/row['path']).read_bytes()) == row['git_blob']
    expected = ['count_all','count_late','trace_coords','tube_three_quarters',
                'target_one_mass','realized_unconditionally']
    assert receipt['axiom_report'].splitlines() == [
        f"'TargetOne.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in expected]
    assert (ROOT/'Gaussian_Target_One.pdf').read_bytes().startswith(b'%PDF')
    assert len(list(ROOT.rglob('*.tex'))) == len(list(ROOT.rglob('*.pdf'))) == 1
    print('Verified source hashes, dependency order, 64 kernel entries, six axiom closures and manuscript pair.')


if __name__ == '__main__':
    audit()
