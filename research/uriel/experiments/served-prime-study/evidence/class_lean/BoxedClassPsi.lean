import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin

noncomputable section

namespace Uriel.ServedPrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

/-- The three signed functions used in the joint inert-class indicator. -/
def ClassFunction (D : D7) (f : ℕ → ℂ) : Prop :=
  f = psDir D.host.q ∨ f = chDir D.host.d ∨ f = fun a => chDir D.host.d a * psDir D.host.q a

/-- Restriction of a source rectangle to the real axis. -/
theorem noExc_of_goodFor {Q : ℝ} (hQ : 0 ≤ Q) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (h : GoodFor Q χ) : QH.NoExc (1 / 400) χ := by
  intro β hb _
  exact h.2.2.2 (β : ℂ) (by simpa using hb) (by simpa using hQ)

/-- Each of the three primitive representatives is covered by its own part of Boxes_at. -/
theorem noExc_of_boxes {D : D7} {Y eps : ℝ} (h : Boxes_at D Y eps)
    {f : ℕ → ℂ} (hf : ClassFunction D f) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : Induces χ f (8 * D.host.q * D.host.d)) : QH.NoExc (1 / 400) χ := by
  obtain ⟨hq, _, hd, _, hqd, _⟩ := h
  have hX : 0 < X1 Y eps := Real.exp_pos _
  have hX' : 0 < X2 Y eps := Real.exp_pos _
  rcases hf with rfl | rfl | rfl
  · exact noExc_of_goodFor (by positivity) (hq N χ hχ)
  · exact noExc_of_goodFor (by positivity) (hd N χ hχ)
  · exact noExc_of_goodFor (by positivity) (hqd N χ hχ)

/-- The constants precede the family and its varying scale and field. The arithmetic
    sum is the source's unsmoothed centered von Mangoldt sum PI.psi0. -/
theorem family_psi_estimate :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (eps : ℝ) (Fm : FamP eps), BoxesF Fm →
      ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ i : Fm.Ix x, ∀ f : ℕ → ℂ,
        ClassFunction (Fm.D x i) f → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          Induces χ f (8 * (Fm.D x i).host.q * (Fm.D x i).host.d) →
          ∀ lam : ℝ, 1 ≤ lam → Real.log N ≤ lam →
          ∀ u : ℝ, Real.exp 1 ≤ u →
          ‖PI.psi0 χ u‖ ≤ C * u * (Real.log u + lam) ^ 2 *
            Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := by
  obtain ⟨C, c, hC, hc, h⟩ := QH.psi_thin (1 / 400) (by norm_num)
  refine ⟨C, c, hC, hc, ?_⟩
  intro eps Fm hBoxes
  obtain ⟨x₀, hBoxes⟩ := hBoxes
  refine ⟨x₀, ?_⟩
  intro x hx i f hf N hN χ hχ lam hlam hcond u hu
  obtain ⟨Y, _, hBox, _⟩ := hBoxes x hx i
  exact h N χ lam hχ.1 hlam hcond (fun _ _ => noExc_of_boxes hBox hf hχ) u hu


/-- Once the logarithmic conductor fits below t^(2/3), the raw centered-sum
error has an envelope independent of the host. -/
theorem conductor_envelope {A c t lam : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (ht : 1 ≤ t) (hlo : 1 ≤ lam) (hhi : lam ≤ t ^ (2 / 3 : ℝ)) :
    A * (t + lam) ^ 2 * Real.exp (-c * t / (lam + Real.sqrt t)) ≤
      4 * A * t ^ 2 * Real.exp (-(c / 2) * t ^ (1 / 3 : ℝ)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hD : 0 < lam + Real.sqrt t := by linarith [Real.sqrt_nonneg t]
  have hx : Real.sqrt t ≤ t ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have hpow : t ^ (2 / 3 : ℝ) ≤ t := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht (show (2/3:ℝ) ≤ 1 by norm_num)
  have hprod : t ^ (1/3 : ℝ) * t ^ (2/3 : ℝ) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have hk := mul_le_mul_of_nonneg_left (show lam + Real.sqrt t ≤ 2 * t ^ (2/3:ℝ) by linarith)
    (Real.rpow_nonneg ht0.le (1/3:ℝ))
  have hexp : -c * t / (lam + Real.sqrt t) ≤ -(c/2) * t ^ (1/3:ℝ) := by
    apply (div_le_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_left hk hc.le
    nlinarith only [hh, congrArg (fun u : ℝ => c * u) hprod]
  have hsq : A * (t + lam)^2 ≤ 4*A*t^2 := by
    have hsum : 0 ≤ t + lam := by linarith
    have hbound : t + lam ≤ 2*t := by linarith
    have huv := pow_le_pow_left₀ hsum hbound 2
    nlinarith only [mul_le_mul_of_nonneg_left huv hA]
  exact mul_le_mul hsq (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)

open Filter Topology in
theorem envelope_tends_to_zero (A c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => 4 * A * t ^ 2 * Real.exp (-(c / 2) * t ^ (1/3:ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (c/2) (by positivity)).comp
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3))
  have hh := h.const_mul (4*A)
  rw [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  dsimp only [Function.comp_apply]
  have hp : (t ^ (1/3:ℝ)) ^ (6:ℝ) = t^2 := by
    rw [← Real.rpow_mul ht]; norm_num
  rw [hp]; ring

#print axioms conductor_envelope
#print axioms envelope_tends_to_zero
#print axioms noExc_of_goodFor
#print axioms noExc_of_boxes
#print axioms family_psi_estimate

end Uriel.ServedPrime
