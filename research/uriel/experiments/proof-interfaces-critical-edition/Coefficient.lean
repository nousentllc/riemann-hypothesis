import New.Reduction.OneSidedBound

open Filter Real

namespace NousInterfaces

/-- Any chosen positive coefficient is available if the exponent has positive slack.
The eventually quantifier is inside all four parameter choices. -/
theorem chosen_coefficient {q : ℕ} [NeZero q] (hq : 18480 ∣ q) {d : ℕ}
    [Fact d.Prime] (hd : d ≡ q / 2 - 1 [MOD q]) {ε A : ℝ}
    (hε : 0 < ε) (hA : 0 < A) :
    ∀ᶠ y : ℝ in atTop, New.primeRemainder d q y ≤ A * y ^ (-1 / 2 + ε) := by
  let C : ℝ := 128 * q.totient + 32
  have htail := New.eventually_primeRemainder_le_mul_rpow hq hd (half_pos hε)
  have hgrowth := (tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop (C / A)
  filter_upwards [htail, hgrowth, eventually_gt_atTop (0 : ℝ)] with y hy hlarge hypos
  have hC : C ≤ A * y ^ (ε / 2) := by
    simpa [mul_comm] using (div_le_iff₀ hA).mp hlarge
  calc
    New.primeRemainder d q y ≤ C * y ^ (-1 / 2 + ε / 2) := hy
    _ ≤ (A * y ^ (ε / 2)) * y ^ (-1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hypos.le _)
    _ = A * y ^ (-1 / 2 + ε) := by
      rw [mul_assoc, ← Real.rpow_add hypos]
      congr 2
      ring

end NousInterfaces
#print axioms NousInterfaces.chosen_coefficient
