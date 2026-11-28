import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic

namespace SlotThree.BaseField

open NumberField

abbrev K := CyclotomicField 3 ℚ

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem class_number : NumberField.classNumber K = 1 :=
  (NumberField.classNumber_eq_one_iff).2 (IsCyclotomicExtension.Rat.three_pid K)

theorem three_not_dvd_class_card : ¬ 3 ∣ Nat.card (ClassGroup (𝓞 K)) := by
  have hc : Nat.card (ClassGroup (𝓞 K)) = 1 := by
    simpa only [NumberField.classNumber, Nat.card_eq_fintype_card] using class_number
  rw [hc]
  decide

theorem root_powers (k : ℕ) : (∃ ζ : K, IsPrimitiveRoot ζ (3 ^ k)) ↔ k ≤ 1 := by
  constructor
  · rintro ⟨ζ, hζ⟩
    have hd := hζ.dvd_of_isCyclotomicExtension 3 (pow_ne_zero k (by decide))
    by_contra! hk
    have h9 : 9 ∣ 2 * 3 := dvd_trans (pow_dvd_pow 3 (show 2 ≤ k by omega)) hd
    norm_num at h9
  · intro hk
    interval_cases k
    · exact ⟨1, by simp⟩
    · exact ⟨IsCyclotomicExtension.zeta 3 ℚ K, by simpa using IsCyclotomicExtension.zeta_spec 3 ℚ K⟩

/-- This supremum is the body of the pinned tower's cZero for this field. -/
theorem maximal_level : sSup {k : ℕ | ∃ ζ : K, IsPrimitiveRoot ζ (3 ^ k)} = 1 := by
  have hs : {k : ℕ | ∃ ζ : K, IsPrimitiveRoot ζ (3 ^ k)} = Set.Iic 1 := by
    ext k
    exact root_powers k
  rw [hs, csSup_Iic]

#print axioms class_number
#print axioms three_not_dvd_class_card
#print axioms root_powers
#print axioms maximal_level

end SlotThree.BaseField
