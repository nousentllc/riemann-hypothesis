"""Replay the original limit cancellation and the group-theoretic norm-index step."""
import argparse
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PIN = '40e56bab026552e089d7afcfeff08d2defb9c005'
SDK = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
DIR = Path('src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition')
HEADER = """import Mathlib
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
namespace GlobalTheory.CompanionTheory.RgBaseCnt
"""
EXTRA = """
#print axioms limit_cancel
end GlobalTheory.CompanionTheory.RgBaseCnt
namespace SWCheck

/-- Group-theoretic part of hEx, with the nontrivial character supplied. -/
theorem norm_kernel_index {G : Type*} [Group G] (χ : G →* ℤˣ)
    (h : ∃ b, χ b ≠ 1) : χ.ker.index = 2 := by
  obtain ⟨b, hb⟩ := h
  have hr : χ.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
  rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- Control: the codomain by itself does not force index two. -/
theorem trivial_index {G : Type*} [Group G] :
    (1 : G →* ℤˣ).ker.index = 1 := by simp

#print axioms norm_kernel_index
#print axioms trivial_index
end SWCheck
end
"""


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ('repo', 'source', 'sdk', 'mathlib'):
        parser.add_argument('--' + key, type=Path, required=True)
    args = parser.parse_args()
    repo, source, sdk, mathlib = [getattr(args, k).resolve() for k in ('repo','source','sdk','mathlib')]
    version = subprocess.check_output([sdk/'bin/lean','--version'], text=True).strip()
    mrev = subprocess.check_output(['git','-C',mathlib,'rev-parse','HEAD'], text=True).strip()
    if SDK not in version or mrev != MATHLIB:
        raise ValueError('Unexpected Lean or Mathlib revision')
    path = DIR/'CountingFormulaOfComponents.lean'
    expected = subprocess.check_output(['git','-C',repo,'rev-parse',PIN+':'+str(path)], text=True).strip()
    data = (source/path).read_bytes()
    if sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() != expected:
        raise ValueError('Original source does not match the pin')
    fragment = b''.join(data.splitlines(keepends=True)[248:273])
    wrapper = HEADER.encode()+fragment+EXTRA.encode()
    with tempfile.TemporaryDirectory() as tmp:
        build = Path(tmp)
        (build/'IndexAndLimit.lean').write_bytes(wrapper)
        paths = [build, mathlib/'.lake/build/lib/lean', *sorted((mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')), sdk/'lib/lean']
        env = dict(os.environ, LEAN_SYSROOT=str(sdk), LEAN_PATH=os.pathsep.join(map(str,paths)))
        logs=[]
        for cmd in ([sdk/'bin/lean','-o','IndexAndLimit.olean','IndexAndLimit.lean'],[sdk/'bin/leanchecker','-v','IndexAndLimit']):
            r=subprocess.run(cmd,cwd=build,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            print(r.stdout,flush=True)
            if r.returncode or 'sorry' in r.stdout: raise SystemExit(r.returncode or 1)
            logs.append(r.stdout.strip())
        if "replaying IndexAndLimit" not in logs[1] or logs[0].count("depends on axioms:") != 3:
            raise ValueError('Missing proof or replay records')
    (HERE/'IndexAndLimit.lean').write_bytes(wrapper)
    receipt = dict(pin=PIN, source=str(path), git_blob=expected, span=[249,273],
        fragment_sha256=sha256(fragment).hexdigest(),module_sha256=sha256(wrapper).hexdigest(),
        lean=version,mathlib=mrev,output=logs,
        scope='Exact original limit_cancel, and new conditional group index lemmas. The global norm theorem and the automorphic limits were traced in source and lie outside this module.')
    (HERE/'receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')


if __name__ == '__main__':
    run()
