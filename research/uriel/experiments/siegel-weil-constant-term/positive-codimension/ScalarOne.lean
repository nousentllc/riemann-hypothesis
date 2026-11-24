import Mathlib

open Filter Topology
open scoped ENNReal NNReal

namespace ScalarOne

/-- Archimedean comparison in the nonzero, one-vector fiber of ambient rank at least three. -/
theorem of_frequent_growth {M D : ℕ} (hM : 3 ≤ M) (hD : 0 < D)
    {c w κ C : ℝ} (hw : 0 < w) (hκ : 0 < κ) (I P : ℕ → ℝ)
    (factor : ∀ a, 0 < a → I a = c * w * P a)
    (error : ∀ a, 0 < a → |I a - w * P a| ≤ C * (a : ℝ) ^ (D * M))
    (growth : ∀ k : ℕ, ∃ a : ℕ, k < a ∧
      κ * (a : ℝ) ^ (D * (2 * M - 2)) ≤ P a) : c = 1 := by
  by_contra hne
  have pos : 0 < |c - 1| * (w * κ) :=
    mul_pos (abs_pos.2 (sub_ne_zero.2 hne)) (mul_pos hw hκ)
  obtain ⟨k, hk⟩ := exists_nat_gt (C / (|c - 1| * (w * κ)))
  obtain ⟨a, ha, lower⟩ := growth k
  have ha0 : 0 < a := lt_of_le_of_lt k.zero_le ha
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha0
  have hP : 0 ≤ P a := le_trans (by positivity) lower
  have upper := error a ha0
  rw [factor a ha0, show c * w * P a - w * P a = (c - 1) * (w * P a) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hw.le hP)] at upper
  have power : (a : ℝ) * (a : ℝ) ^ (D * M) ≤ (a : ℝ) ^ (D * (2 * M - 2)) := by
    rw [← pow_succ']
    refine pow_le_pow_right₀ haR ?_
    obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
    rw [show 2 * (M' + 3) - 2 = M' + 3 + (M' + 1) by omega, mul_add _ (M' + 3)]
    exact Nat.add_le_add_left (Nat.mul_pos hD (Nat.succ_pos _)) _
  have small : |c - 1| * (w * κ) * (a : ℝ) ≤ C := by
    apply le_of_mul_le_mul_right _ (show 0 < (a : ℝ) ^ (D * M) by positivity)
    calc
      _ = |c - 1| * (w * (κ * ((a : ℝ) * (a : ℝ) ^ (D * M)))) := by ring
      _ ≤ |c - 1| * (w * P a) := by
        gcongr
        exact (mul_le_mul_of_nonneg_left power hκ.le).trans lower
      _ ≤ _ := upper
  rw [div_lt_iff₀' pos] at hk
  have larger : (k : ℝ) < a := by exact_mod_cast ha
  exact (not_lt_of_ge small) (hk.trans (mul_lt_mul_of_pos_left larger pos))

/-- The last comparison in the anisotropic binary calculation. Both rescaled masses
    tend to the same finite, nonzero volume and the scaled densities agree eventually. -/
theorem of_common_mass {ι : Type*} {f : Filter ι} [f.NeBot]
    {μ ν : ι → ℝ≥0∞} {V : ℝ≥0∞} {c : ℝ≥0}
    (nonzero : V ≠ 0) (finite : V ≠ ⊤)
    (left : Tendsto μ f (𝓝 V)) (right : Tendsto ν f (𝓝 V))
    (factor : μ =ᶠ[f] fun t => (c : ℝ≥0∞) * ν t) : c = 1 := by
  have scaled := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) right (Or.inr ENNReal.coe_ne_top)
  have same : V = (c : ℝ≥0∞) * V := tendsto_nhds_unique left (scaled.congr' factor.symm)
  have eq : (c : ℝ≥0∞) * V = 1 * V := by
    rw [one_mul]
    exact same.symm
  have c_one := (ENNReal.mul_left_inj nonzero finite).1 eq
  exact_mod_cast c_one

#print axioms of_frequent_growth
#print axioms of_common_mass

end ScalarOne
