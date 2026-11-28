import Mathlib

open Filter Real
namespace EndpointRegularity

/-- An arbitrary fixed multiplicative constant is absorbed in a strict power margin. -/
theorem absorb {a b : ℝ} (h : a < b) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C * t ^ a ≤ t ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop C,
    eventually_ge_atTop (1:ℝ)] with t hC ht
  have hp : 0 < t := by linarith
  calc
    C * t ^ a ≤ t ^ (b-a) * t ^ a := mul_le_mul_of_nonneg_right hC (rpow_nonneg hp.le _)
    _ = t ^ b := by rw [← rpow_add hp]; ring_nf

/-- A fixed positive slope bound gives a power-width exterior neighborhood, using
only a level comparison at the anchor t and uniform thresholds chosen before t. -/
theorem extend {g : ℝ → ℝ} {K s θ : ℝ} (hK : 0 < K) (hs : s < θ)
    (hθ : 0 ≤ θ) (hu : θ < 1)
    (hL : ∀ x ≥ (1:ℝ), ∀ y ≥ (1:ℝ), |g y-g x| ≤ K*|y-x|) :
    ∀ᶠ t : ℝ in atTop, g t ≤ t^s → ∀ y ≥ (1:ℝ), |y-t| ≤ t^θ/(4*K) → g y ≤ y^θ := by
  filter_upwards [absorb hs 4, absorb hu (1/(2*K)), eventually_ge_atTop (1:ℝ)] with t h1 h2 ht
  intro hgt y hy hd
  have ht' : 0 < t := by linarith
  rw [rpow_one] at h2
  have hkr : 0 < 4*K := by positivity
  have hsmall : t^θ/(4*K) ≤ t/2 := by
    field_simp [ne_of_gt hK] at h2 ⊢
    nlinarith
  have hyt : t/2 ≤ y := by
    have h := (abs_le.mp hd).1
    linarith
  have hG := (abs_le.mp (hL t ht y hy)).2
  have hc := (le_div_iff₀ hkr).mp hd
  have hbase := rpow_le_rpow (by positivity : 0 ≤ t/2) hyt hθ
  have hscale : (2:ℝ)^θ ≤ 2 := by
    calc (2:ℝ)^θ ≤ (2:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) hu.le
         _ = 2 := rpow_one _
  rw [div_rpow ht'.le (by norm_num)] at hbase
  have h2pos : (0:ℝ) < 2^θ := by positivity
  have h := (div_le_iff₀ h2pos).mp hbase
  have h3 := mul_le_mul_of_nonneg_left hscale (rpow_nonneg (by linarith : 0 ≤ y) θ)
  linarith

#print axioms absorb
#print axioms extend

end EndpointRegularity
