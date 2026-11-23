import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic

noncomputable section
namespace SlotSevenProbe
open NumberField NumberField.InfinitePlace Ideal IsCyclotomicExtension.Rat
theorem seven_pid (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let M : ℝ := (4 / Real.pi) ^ nrComplexPlaces K *
    ((Nat.factorial (Module.finrank ℚ K) : ℝ) / (Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) *
      Real.sqrt |(NumberField.discr K : ℝ)|)
  have hm : ⌊M⌋₊ ≤ 4 := by
    have hdeg : Module.finrank ℚ K = 6 := (IsCyclotomicExtension.Rat.finrank 7 K).trans (by decide)
    have hdisc : discr K = -16807 := (discr_prime 7 K).trans (by decide)
    have hpl : nrComplexPlaces K = 3 := (nrComplexPlaces_eq_totient_div_two 7 (K := K)).trans (by decide)
    have hs : Real.sqrt 16807 ≤ 130 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have hp : 4 / Real.pi ≤ 40 / 31 := (div_le_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_d2])
    apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt' (by decide : 5 ≠ 0)).2
    dsimp [M]
    rw [hdeg, hdisc, hpl]
    rw [show |(((-16807 : ℤ) : ℝ))| = 16807 by norm_num]
    change (4 / Real.pi)^3 * ((720 : ℝ) / 6^6 * Real.sqrt 16807) < 5
    calc
      _ ≤ (40 / 31 : ℝ) ^ 3 * (720 / 6 ^ 6 * 130) := by gcongr
      _ < 5 := by norm_num
  have h₂ : orderOf (2 : ZMod 7) = 3 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, fun m hm hp => ?_⟩
    interval_cases m <;> decide
  have h₃ : orderOf (3 : ZMod 7) = 6 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, fun m hm hp => ?_⟩
    interval_cases m <;> decide
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp prime P hP hpN
  change p ^ P.inertiaDeg ℤ ≤ ⌊M⌋₊ at hpN
  obtain ⟨hprime, hlies⟩ := hP
  have hsmall : p ≤ 4 := (Finset.mem_Icc.mp hp).2.trans hm
  have hcases : p = 2 ∨ p = 3 := by interval_cases p <;> norm_num at *
  rcases hcases with rfl | rfl
  · have hf := inertiaDeg_eq_of_not_dvd 2 K P (m := 7) (by decide)
    rw [show (2 : ZMod 7) = (2 : ℕ) from rfl] at h₂
    rw [hf, h₂] at hpN
    exact (by omega : False).elim
  · have hf := inertiaDeg_eq_of_not_dvd 3 K P (m := 7) (by decide)
    rw [show (3 : ZMod 7) = (3 : ℕ) from rfl] at h₃
    rw [hf, h₃] at hpN
    exact (by omega : False).elim

theorem base_class_number : NumberField.classNumber (CyclotomicField 7 ℚ) = 1 := by
  let _ : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) := CyclotomicField.isCyclotomicExtension 7 ℚ
  exact NumberField.classNumber_eq_one_iff.mpr (seven_pid _)

/-- The starting condition of a seven-primary ascent, for any model of the base field. -/
theorem seven_not_dvd_class (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {7} ℚ K] : ¬ 7 ∣ Nat.card (ClassGroup (𝓞 K)) := by
  have h : NumberField.classNumber K = 1 := NumberField.classNumber_eq_one_iff.mpr (seven_pid K)
  rw [Nat.card_eq_fintype_card]
  change ¬ 7 ∣ NumberField.classNumber K
  rw [h]
  decide

#print axioms seven_pid
#print axioms base_class_number
#print axioms seven_not_dvd_class
end SlotSevenProbe
