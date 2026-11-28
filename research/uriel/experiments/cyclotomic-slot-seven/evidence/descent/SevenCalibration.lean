import SevenConclusions

open NumberField Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Kum UpperTheory.V.Tower
  UpperTheory.V.Win UpperTheory.V.LDataCardLeFinrank Seven.Descent Seven.CyclotomicTransport

namespace Seven.Calibration

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ L := CyclotomicField.isCyclotomicExtension 7 ℚ

theorem rootLevel (k : ℕ) : (∃ ζ : L, IsPrimitiveRoot ζ (7^k)) ↔ k ≤ 1 := by
  constructor
  · rintro ⟨ζ,hζ⟩
    have hd := hζ.dvd_of_isCyclotomicExtension 7 (pow_ne_zero k (by decide))
    by_contra! hk
    have h49 : 49 ∣ 2 * 7 := dvd_trans (pow_dvd_pow 7 (show 2 ≤ k by omega)) hd
    norm_num at h49
  · intro hk
    interval_cases k
    · exact ⟨1, by simp⟩
    · exact ⟨IsCyclotomicExtension.zeta 7 ℚ L, by simp [IsCyclotomicExtension.zeta_spec]⟩

theorem baseOffset : cZero 7 L = 1 := by
  unfold cZero
  have hs : {k : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (7^k)} = Set.Iic 1 := by
    ext k
    exact rootLevel k
  rw [hs,csSup_Iic]

theorem zeroRankIndex : jZero 7 0 = 3 := by decide

/-- The zero-cap anchor layer is the fourth cyclotomic-root level. -/
theorem zeroRankField :
    layF 7 L (AlgebraicClosure L) (jZero 7 0) = Layer 4 := by
  unfold layF Layer
  rw [baseOffset, zeroRankIndex]

theorem calibratedLayer :
    IsLayer 7 3 L (Layer 4) ∧ Module.finrank ℚ (Layer 4) = 2058 := by
  constructor
  · have h := (layerUniq L (AlgebraicClosure L) 7 muSeven).1 (jZero 7 0)
    rwa [zeroRankField,zeroRankIndex] at h
  · let : IsCyclotomicExtension {7^4} ℚ (Layer 4) := rational_cyclotomic 4 (by decide)
    rw [IsCyclotomicExtension.Rat.finrank (7^4) (Layer 4), Nat.totient_prime_pow_succ (by decide : Nat.Prime 7)]
    norm_num

end Seven.Calibration

#print axioms Seven.Calibration.rootLevel
#print axioms Seven.Calibration.baseOffset
#print axioms Seven.Calibration.zeroRankIndex
#print axioms Seven.Calibration.zeroRankField
#print axioms Seven.Calibration.calibratedLayer
