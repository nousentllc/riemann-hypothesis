"""Replay the minimal-rank modification of the pinned coherent supply proof."""
from pathlib import Path
import hashlib
import json

def derive(src):
    text = src.split('theorem coherentJoint ', 1)[1].split('\nopen IsDedekindDomain', 1)[0]
    # Preserve the proof of the field bounds after changing its rank witness.
    text = text.replace('1 ≤ K.CK ∧ ∀ Ct', '''1 ≤ K.CK ∧
      (∀ (l : ℕ) (A : AbF), ZeroRank l A → K.Rl l A = 0) ∧ ∀ Ct''', 1)
    text = text.replace('then Classical.choose h else 0','then Nat.find h else 0')
    text = text.replace('Classical.choose hP','Nat.find hP').replace('Classical.choose_spec hP','Nat.find_spec hP')
    text = text.replace('hCKpos, hCK1, fun Ct hCt => ?_⟩','''hCKpos, hCK1, ?_, fun Ct hCt => ?_⟩
  · intro l A hz
    have hzero : P l A 0 := hz
    have hex : ∃ R, P l A R := ⟨0,hzero⟩
    change (if h : ∃ R, P l A R then Nat.find h else 0) = 0
    rw [dif_pos hex]
    exact Nat.le_zero.mp (Nat.find_min' hex hzero)''',1)
    return '''import SuccessiveFields
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields SynchronizedSlots
noncomputable section
namespace Seven.Ranks

def ZeroRank (l : ℕ) (A : AbF) : Prop :=
  ∃ (_ : Fact l.Prime) (F : Type) (_ : Field F) (_ : NumberField F), IsAbField A F ∧ ABound l 0 F

theorem coherentLeast ''' + text + '\nend Seven.Ranks\nend\n#print axioms Seven.Ranks.coherentLeast\n'

if __name__ == "__main__":
    here = Path(__file__).resolve().parent
    research = json.loads((here.parent/"prior_sources.json").read_text())
    source = research["SuccessiveFields"]
    expected = hashlib.sha1(b"blob " + str(len(source.encode())).encode() + b"\0" + source.encode()).hexdigest()
    assert expected == json.loads((here.parent/"prior_pins.json").read_text())["SuccessiveFields"]["blob"]
    assert (here/"LeastSupply.lean").read_text() == derive(source)
    print("Verified the derivation of LeastSupply.lean from the pinned previous supply.")
