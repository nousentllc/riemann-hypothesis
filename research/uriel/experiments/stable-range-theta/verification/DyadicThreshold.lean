import Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory Topology
namespace UrielCheck

theorem integrable_of_count_at {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j)
    (t₀ : ℝ) (h₀ : 0 ≤ t₀) (hgeo : (1 / 2 : ℝ) ^ t₀ * (b : ℝ) < 1) :
    ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by
  classical
  intro t ht
  refine ⟨(hf.pow_const t).aestronglyMeasurable, ?_⟩
  have t0 : 0 ≤ t := h₀.trans ht
  let P : ℕ → Set G := fun j => {g | (1 / 2) ^ j ≤ f g ∧ f g ≤ 2 * R * (1 / 2) ^ j}
  have hP : ⋃ j, P j = Set.univ := Set.eq_univ_of_forall fun g => by
    have ex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ f g := (exists_pow_lt_of_lt_one (h0 g) (by norm_num)).imp fun _ => le_of_lt
    refine Set.mem_iUnion.2 ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
    rcases e : Nat.find ex with _ | j
    · have := hR g; simp; linarith
    · have := Nat.find_min ex (m := j) (by omega)
      have p : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [pow_succ]; nlinarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) ^ t) * b
  have hρ : ρ < 1 := by
    have hp : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
    rw [show ρ = ENNReal.ofReal ((1 / 2) ^ t * b) by
      rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_coe_nnreal], ENNReal.ofReal_lt_one]
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht) b.2).trans_lt hgeo
  calc ∫⁻ g, ‖f g ^ t‖ₑ ∂μ = ∫⁻ g in ⋃ j, P j, ‖f g ^ t‖ₑ ∂μ := by rw [hP, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ g in P j, ‖f g ^ t‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal ((2 * R) ^ t) * C * ρ ^ j := ENNReal.tsum_le_tsum fun j => by
      refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((2 * R) ^ t) * ENNReal.ofReal ((1 / 2) ^ t) ^ j)
        measurable_const fun g hg => ?_).trans ?_
      · rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (h0 g).le _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul_natCast (by norm_num), mul_comm t, Real.rpow_natCast_mul (by norm_num),
          ← Real.mul_rpow (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (h0 g).le hg.2 t0)
      · rw [setLIntegral_const]
        refine (mul_le_mul_right ((measure_mono fun g hg => hg.1).trans (h j)) _).trans_eq ?_
        simp only [ρ, mul_pow]; ring
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))

/-- For b = 2^α the new ratio is strictly below one at every t > α. -/
theorem ratio_past_power (α : ℕ) (t : ℝ) (ht : (α : ℝ) < t) :
    (1 / 2 : ℝ) ^ t * (2 : ℝ) ^ α < 1 := by
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, div_mul_eq_mul_div,
      one_mul, div_lt_one (by positivity), ← Real.rpow_natCast]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ht

/-- Actual specialization of the shell bound for an eligible real exponent.
    Neither an automorphic model nor a theta lift is assumed or constructed. -/
theorem integrable_power_after {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ}
    (hf : Measurable f) (h0 : ∀ g, 0 < f g) {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (α : ℕ)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * (((2 : ℝ≥0) ^ α : ℝ≥0) : ℝ≥0∞) ^ j)
    (t : ℝ) (ht : (α : ℝ) < t) : Integrable (fun g => f g ^ t) μ := by
  apply integrable_of_count_at μ hf h0 h1 hR hC ((2 : ℝ≥0) ^ α) h t
    ((Nat.cast_nonneg α).trans ht.le) _ t le_rfl
  simpa using ratio_past_power α t ht

/-- The source's more conservative sufficient condition at the explicit integer. -/
theorem ratio_at_integer (L : ℕ) :
    (1 / 2 : ℝ) ^ (2 + L) < 1 / ((2 : ℝ) ^ (1 + L) + 1) := by
  have h : (1 : ℝ) < 2 ^ (1 + L) := one_lt_pow₀ (by norm_num) (by omega)
  rw [one_div, inv_pow, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
  rw [show 2 + L = (1 + L) + 1 by omega, pow_succ]
  linarith

/-- With the real threshold below, every integer rank at this floor gives a
strict gap between t₀ and d/2. This is arithmetic only. -/
theorem quarter_gap (D n d : ℕ) (hd : 3 + 16 * D * n ^ 2 ≤ d) :
    ((1 + 8 * D * n ^ 2 : ℕ) : ℝ) + 1 / 4 < (d : ℝ) / 2 := by
  have h : (3 : ℝ) + 16 * D * (n : ℝ) ^ 2 ≤ d := by exact_mod_cast hd
  push_cast
  linarith

#print axioms GlobalTheory.ThK.Dbl.Hgt.integrable_of_count
#print axioms UrielCheck.integrable_power_after
#print axioms UrielCheck.integrable_of_count_at
#print axioms UrielCheck.ratio_past_power
#print axioms UrielCheck.ratio_at_integer
#print axioms UrielCheck.quarter_gap
end UrielCheck
end
