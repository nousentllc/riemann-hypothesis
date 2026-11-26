import Mathlib

open scoped BigOperators
namespace GlobalFrobenius

/-- Original expected-cost proof can intersect with a prescribed event
    whose failure has small mass. The conclusion keeps the same outcome. -/
theorem choose_with_event {Ω : Type*} [Fintype Ω] (w cost : Ω → ℝ)
    (event : Ω → Prop) [DecidablePred event]
    (hw : ∀ a, 0 ≤ w a) (hNonneg : ∀ a, 0 ≤ cost a) (hMass : ∑ a, w a = 1)
    {c : ℝ} (hCost : ∑ a, w a * cost a ≤ c)
    (hFail : ∑ a, w a * (if event a then 0 else 1) < 1-c) :
    ∃ a, 0 < w a ∧ cost a ≤ 1 ∧ event a := by
  classical
  by_contra! h
  have hpoint (a : Ω) : w a ≤ w a * cost a + w a * (if event a then 0 else 1) := by
    by_cases z : w a = 0
    · simp [z]
    · have hp : 0 < w a := lt_of_le_of_ne (hw a) (Ne.symm z)
      by_cases e : event a
      · have v : 1 < cost a := lt_of_not_ge (fun hl => h a hp hl e)
        simpa [e] using (mul_le_mul_of_nonneg_left v.le hp.le)
      · simp [e, mul_nonneg hp.le (hNonneg a)]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  rw [Finset.sum_add_distrib, hMass] at hs
  linarith

/-- The old normalized count and bad-mass budget survive adding a separately
    protected prime and a rare failure event. -/
theorem keep_original_budget {Ω : Type*} [Fintype Ω] (w A B E : Ω → ℝ)
    (event : Ω → Prop) [DecidablePred event]
    (hw : ∀ a, 0 ≤ w a) (hMass : ∑ a, w a = 1)
    (hA0 : ∀ a, 0 ≤ A a) (hB0 : ∀ a, 0 ≤ B a) (hE0 : ∀ a, 0 ≤ E a)
    (hA : ∑ a, w a * A a ≤ 1/2) (hB : ∑ a, w a * B a ≤ 1/4)
    (hE : ∑ a, w a * E a ≤ 1/8)
    (hFail : ∑ a, w a * (if event a then 0 else 1) < 1/8) :
    ∃ a, 0 < w a ∧ A a ≤ 1 ∧ B a ≤ 1 ∧ E a ≤ 1 ∧ event a := by
  let cost := fun a => A a + B a + E a
  have hc a : 0 ≤ cost a := by dsimp [cost]; linarith [hA0 a,hB0 a,hE0 a]
  have cost_bound : ∑ a, w a * cost a ≤ (7/8 : ℝ) := by
    simp only [cost, mul_add, Finset.sum_add_distrib]
    linarith
  obtain ⟨a,ha,hs,he⟩ := choose_with_event w cost event hw hc hMass cost_bound
    (by linarith)
  dsimp [cost] at hs
  exact ⟨a,ha,by linarith [hB0 a,hE0 a],by linarith [hA0 a,hE0 a],
    by linarith [hA0 a,hB0 a],he⟩

/-- Chebyshev lower deviation on the same finite law. The second-moment
    bound is the only probabilistic input to this kernel-checked implication. -/
theorem half_mean_failure {Ω : Type*} [Fintype Ω] (w Z : Ω → ℝ)
    {μ : ℝ} (hμ : 0 < μ) (hw : ∀ a, 0 ≤ w a)
    (hvar : ∑ a, w a * (Z a - μ)^2 ≤ μ) :
    (∑ a, w a * (if Z a < μ/2 then 1 else 0)) ≤ 4/μ := by
  have v (a : Ω) :
      w a * (if Z a < μ/2 then 1 else 0) ≤ (4/μ^2) * (w a * (Z a-μ)^2) := by
    split_ifs with h
    · have h1 : (μ/2)^2 ≤ (μ-Z a)^2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h2 : 1 ≤ (4 / μ ^ 2) * (Z a-μ)^2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hμ)]
        nlinarith only [h1]
      calc
        w a * 1 ≤ w a * ((4/μ^2) * (Z a-μ)^2) :=
          mul_le_mul_of_nonneg_left h2 (hw a)
        _ = _ := by ring
    · rw [mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (hw a) (sq_nonneg _))
  calc
    _ ≤ ∑ a, (4/μ^2) * (w a * (Z a-μ)^2) := Finset.sum_le_sum fun a _ => v a
    _ = (4/μ^2) * ∑ a, w a * (Z a-μ)^2 := by rw [Finset.mul_sum]
    _ ≤ (4/μ^2) * μ := mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = _ := by field_simp

/-- Having more collision anchors than failed points yields a collision on a
    certified good orbit. Both sets are on one choice of mask and prime. -/
theorem some_collision_not_bad {A : Type*} (collisions bad : Finset A)
    (h : bad.card < collisions.card) :
    ∃ a ∈ collisions, a ∉ bad := by
  classical
  by_contra! H
  exact h.not_ge (Finset.card_le_card H)

/-- If the weighted exceptional score is too small to absorb all
    collision incidences, a good collision survives on the same set. -/
theorem weighted_good_collision {I : Type*} [Fintype I] (weight collision bad : I → ℝ)
    {lower : ℝ} (hw : ∀ i, lower ≤ weight i) (hc : ∀ i, 0 ≤ collision i)
    (hbad : ∑ i, weight i * bad i < lower * ∑ i, collision i) :
    (∀ i, 0 ≤ weight i) → ∃ i, bad i < collision i := by
  intro hn
  by_contra! H
  have hle : lower * (∑ i, collision i) ≤ ∑ i, weight i * bad i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hw i) (hc i)).trans
        (mul_le_mul_of_nonneg_left (H i) (hn i))
  exact hbad.not_ge hle

end GlobalFrobenius

#print axioms GlobalFrobenius.choose_with_event
#print axioms GlobalFrobenius.some_collision_not_bad
#print axioms GlobalFrobenius.keep_original_budget
#print axioms GlobalFrobenius.half_mean_failure
#print axioms GlobalFrobenius.weighted_good_collision
