import Mathlib

open Filter

namespace ExceptionalBand

/-- The exponent of the raw logarithm of the exceptional-weight envelope. -/
theorem raw_power {x k n d N D a r C : ℝ} (hx : 0 < x)
    (hk : 0 ≤ k) (hn : 0 ≤ n) (hnN : n ≤ N) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (hkx : k ≤ x ^ a) (hd : d ≤ D * x ^ r) :
    (2 * k * n) ^ C * d ≤ (2 * N) ^ C * D * x ^ (a * C + r) := by
  have hN := hn.trans hnN
  have hxk : 2 * k * n ≤ (2 * N) * x ^ a := by
    calc 2 * k * n = 2 * (n * k) := by ring
         _ ≤ 2 * (N * x ^ a) := by gcongr
         _ = (2 * N) * x ^ a := by ring
  have ht := Real.rpow_le_rpow (by positivity : 0 ≤ 2*k*n) hxk hC
  have hp := mul_le_mul_of_nonneg_right ht (mul_nonneg hD (Real.rpow_nonneg hx.le r))
  calc
    (2*k*n)^C * d ≤ (2*k*n)^C * (D * x^r) :=
      mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg (by positivity) _)
    _ ≤ ((2*N) * x^a)^C * (D * x^r) := hp
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
        Real.rpow_add hx]
      ring

/-- Any fixed logarithmic overhead and strictly lower power are absorbed. -/
theorem absorbs {A B s t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hst : s < t) :
    ∀ᶠ x in atTop, A * Real.log x + B * x ^ s ≤ x ^ t := by
  have h1 := ((isLittleO_log_rpow_atTop ht).const_mul_left A).bound
    (by norm_num : (0:ℝ) < 1/2)
  have h2 := (tendsto_rpow_atTop (sub_pos.mpr hst)).eventually_ge_atTop (2*B)
  filter_upwards [h1, h2, eventually_ge_atTop (1:ℝ)] with x hlog hpow hx
  have hx0 : 0 < x := by linarith
  have hxs := Real.rpow_nonneg hx0.le s
  have hxt := Real.rpow_nonneg hx0.le t
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hA (Real.log_nonneg hx)), abs_of_nonneg hxt] at hlog
  have hsplit : x^s * x^(t-s) = x^t := by rw [← Real.rpow_add hx0]; congr 1; ring
  have hb := mul_le_mul_of_nonneg_left hpow hxs
  nlinarith

theorem endpoint_fails {x t B : ℝ} (hx : 0 < x) (hB : 1 < B) :
    x^t < B * x^t := by
  simpa using mul_lt_mul_of_pos_right hB (Real.rpow_pos_of_pos hx t)

theorem active_only {t : ℕ} {Exc : Finset ℕ} {W : ℕ → ℝ} {B : ℝ}
    (regular : ∀ k ∈ Finset.Ico 1 t, k ∉ Exc → W k ≤ B)
    (exceptional : ∀ k ∈ Finset.Ico 1 t, k ∈ Exc → W k ≤ B) :
    ∑ k ∈ Finset.Ico 1 t, W k ≤ (Finset.Ico 1 t).card • B := by
  calc ∑ k ∈ Finset.Ico 1 t, W k ≤ ∑ _k ∈ Finset.Ico 1 t, B := by
         apply Finset.sum_le_sum
         intro k hk
         by_cases h : k ∈ Exc
         · exact exceptional k hk h
         · exact regular k hk h
       _ = _ := by simp

theorem moving_boundary {a : ℝ} : a + 1/4 < 4/5 ↔ a < 11/20 := by constructor <;> intro h <;> linarith

#print axioms raw_power
#print axioms absorbs
#print axioms endpoint_fails
#print axioms active_only
#print axioms moving_boundary

end ExceptionalBand
