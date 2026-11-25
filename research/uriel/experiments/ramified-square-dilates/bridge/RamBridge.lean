import RamBase
import RamLift
import RamGlobal
import RamFieldIntegers
import RamTransportForm

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open scoped ENNReal
noncomputable section
namespace RamBridge

abbrev K := RamField.K
abbrev J : Matrix (Fin 3) (Fin 3) RamGlobal.E := 1
abbrev H := RamTransportForm.H RamGlobal.conjG K
abbrev W := RamTransportForm.W (F:=RamGlobal.F) (E:=RamGlobal.E) K
abbrev MFamily := RamTransportForm.family RamGlobal.conjG J RamGlobal.gb K
abbrev L := RamTransportForm.lattice RamGlobal.gb K RamField.integers
abbrev atFour := hermScal K RamGlobal.conjG 4

theorem normalized (k : ℕ) :
    128*TargetOne.count 6 (4:RamField.R (k+5)) = 257*((2^(k+5))^2)^5 :=
  RamLift.normalized_from_base RamBase.count_four k

/-- All choices of the original disintegration have the same value here. -/
theorem mass_four (lam : Measure K) (hl : lam.IsAddHaarMeasure)
    (hO : lam RamField.integers = 1) (m : H → Measure W) (hm : MFamily lam m) :
    m atFour L = (257/128:ℝ≥0∞) :=
  RamTransportForm.mass_at_four RamGlobal.conjG J RamGlobal.gb RamGlobal.isCM RamGlobal.herm_id
    RamGlobal.gram_matrix normalized lam hl hO m hm

/-- The normalized Haar measure and the family in the preceding statement exist. -/
theorem realized : ∃ lam : Measure K, lam.IsAddHaarMeasure ∧ lam RamField.integers=1 ∧
    ∃ m : H → Measure W, MFamily lam m ∧ m atFour L=(257/128:ℝ≥0∞) :=
  RamTransportForm.realized RamGlobal.conjG J RamGlobal.gb RamGlobal.isCM RamGlobal.herm_id
    RamGlobal.gram_matrix normalized

end RamBridge
#print axioms RamBridge.normalized
#print axioms RamBridge.mass_four
#print axioms RamBridge.realized
