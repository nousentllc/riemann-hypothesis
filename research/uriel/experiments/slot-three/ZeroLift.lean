import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply

noncomputable section

namespace SlotThree

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev ZMat (K : Type) := Matrix (Fin 1) (Fin 1) K

/-- The columns of the zero matrix lift the action through the single zero generator.
The same matrix satisfies the determinant bound in PropA.lift. -/
theorem zero_matrix_lift (X : Type) [AddCommGroup X] [Module ℤ_[3] X] [Subsingleton X]
    (A : Module.End ℤ_[3] X) :
    ∃ π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] X, Function.Surjective π ∧
      (∀ v, π ((0 : ZMat ℤ_[3]).mulVec v) = (A ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ∀ a : ℤ_[3], UpperTheory.V.PropA.cokLen (l := 3) (X := X)
        (a • A ^ (3 ^ 3 : ℕ) - (1 : Module.End ℤ_[3] X)) ≤
        UpperTheory.V.PropA.vl 3 (a • (0 : ZMat ℤ_[3]) - 1).det := by
  refine ⟨0, fun x => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _, ?_⟩
  intro a
  rw [UpperTheory.V.PropA.cokLen, Module.length_eq_zero]
  exact bot_le

/-- Over the same algebraic closure used in detBound the characteristic roots consist of zero. -/
theorem zero_lift_spectrum :
    (0 : ZMat (PadicAlgCl 3)).charpoly.roots = {0} ∧
    ∀ a : PadicAlgCl 3, (a • (0 : ZMat (PadicAlgCl 3)) - 1).det =
      ∏ _i : Fin 1, (a * 0 - 1) := by
  constructor
  · simp [Matrix.charpoly_zero]
  · intro a
    simp

/-- The exact ball inequality at j=3, c=1 and root zero, for every proposed center. -/
def ZeroRootBall (u s : ℤ_[3]) : Prop :=
  ∀ e : ℕ, ((3 : ℝ) ^ ((3 : ℕ) + 1))⁻¹ * ‖s - e‖ ≤
    ‖algebraMap ℚ_[3] (PadicAlgCl 3) (((u ^ (3 ^ 3 : ℕ)) ^ e : ℤ_[3]) : ℚ_[3]) * 0 - 1‖

theorem zero_root_any_center (u s : ℤ_[3]) : ZeroRootBall u s := by
  intro e
  simp only [mul_zero, zero_sub, norm_neg, norm_one]
  calc
    ((3 : ℝ) ^ ((3 : ℕ) + 1))⁻¹ * ‖s - e‖ ≤ ((3 : ℝ) ^ ((3 : ℕ) + 1))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
    _ ≤ 1 := by norm_num

/-- Fix the arithmetic module, its endomorphism, j, lift, root and cyclotomic value.
The ball condition admits two centers with opposite strict-filter membership at weight one. -/
theorem same_lift_opposite
    (hX : Subsingleton (UpperTheory.V.Tower.XP 3 (CyclotomicField 3 ℚ)))
    (A : Module.End ℤ_[3] (UpperTheory.V.Tower.XP 3 (CyclotomicField 3 ℚ))) (u : ℤ_[3]) :
    (∃ π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] UpperTheory.V.Tower.XP 3 (CyclotomicField 3 ℚ),
      Function.Surjective π ∧ ∀ v, π ((0 : ZMat ℤ_[3]).mulVec v) = (A ^ (3 ^ 3 : ℕ)) (π v)) ∧
    (0 : ZMat (PadicAlgCl 3)).charpoly.roots = {0} ∧
    ZeroRootBall u 0 ∧ ZeroRootBall u 1 ∧
    ¬ ‖(0 : ℚ_[3]) - 1‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) ∧
    ‖(1 : ℚ_[3]) - 1‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)) := by
  let _ := hX
  obtain ⟨π, hs, he, _⟩ := zero_matrix_lift _ A
  refine ⟨⟨π, hs, he⟩, zero_lift_spectrum.1, zero_root_any_center _ _,
    zero_root_any_center _ _, ?_, ?_⟩
  all_goals rw [show Nat.log 3 64 = 3 by decide]
  all_goals norm_num

#print axioms SlotThree.zero_matrix_lift
#print axioms SlotThree.zero_lift_spectrum
#print axioms SlotThree.zero_root_any_center
#print axioms SlotThree.same_lift_opposite

end SlotThree
end
