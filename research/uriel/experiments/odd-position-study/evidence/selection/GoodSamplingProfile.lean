import JointParitySelection
import Development.AutomorphicArithmetic.ThickFrames.orbitSum
import Development.AutomorphicArithmetic.ThickFrames.orbitTerms
import Development.AutomorphicArithmetic.ThickFrames.NotGoodLe
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

namespace Uriel.OddPositions

/-- Freely choose a bounded pointwise sampling profile before selecting the top set.
    The literal Good-orbit test and its weighted bad budget are the original ones.
    The separate signed tests may use unrelated nonnegative weights. -/
theorem goodWithSamplingProfile :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (L₂ : ℕ),
      (Fintype.card A : ℝ) ≤ Co * x ^ hE eps → (L₂ : ℝ) ≤ Lb →
      ∀ bs : A → A → A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) →
      (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∀ (π : A → ℝ), (∀ a, 3 / 4 * dE eps x ≤ π a ∧ π a ≤ dE eps x) →
      ∀ (S : Finset ℕ) (v : ℕ → ℝ) (σ : ℕ → A → ℝ), (∀ i ∈ S, 0 ≤ v i) →
      0 < ∑ i ∈ S, v i → (∀ i ∈ S, ∀ a, (σ i a)^2 ≤ 1) →
      ∃ T : Finset A, |(T.card : ℝ) - ∑ a, π a| ≤ Real.sqrt (2 * dE eps x * Fintype.card A) ∧
        (∑ p ∈ PP, ω p * (({t : A | t ∈ T ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * Fintype.card A * ∑ p ∈ PP, ω p) ∧
        (∑ i ∈ S, v i * (dev π (σ i) T)^2) ≤ 4 * (dE eps x * Fintype.card A * ∑ i ∈ S, v i) := by
  intro eps Co Lb he
  obtain ⟨Cb, x₀, hCb, hnum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms eps Co Lb he
  refine ⟨Cb, max x₀ 1, hCb, ?_⟩
  intro x hx A _ _ _ L₂ hhi hL bs hbs PP hp ω hω hPP π hp1 S v σ hv hMass hσ
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hxx0 : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hδ : 0 < dE eps x := Real.rpow_pos_of_pos hx0 _
  have hδ1 : dE eps x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hN0 : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hβ : 0 ≤ Cb * x ^ (-2 : ℝ) := by positivity
  have hD : 0 < Real.sqrt (2 * dE eps x * Fintype.card A) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨T, hT1, hT2, hT3⟩ := selectWithWeightedSigns A Unit ℕ ℕ (fun _ => ()) π (dE eps x)
    (Cb * x ^ (-2 : ℝ)) (Real.sqrt (2 * dE eps x * Fintype.card A)) PP ω
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (KE eps) (rE eps)
      (dE eps x) (hE eps) x)
    (fun a => ⟨le_trans (by positivity) (hp1 a).1, (hp1 a).2⟩) hδ hδ1 hβ hω hD
    (le_of_eq (Real.sq_sqrt (by positivity)).symm) (by
      intro p hpp t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ Co * x ^ hE eps :=
        le_trans (Nat.cast_le.mpr addOrderOf_le_card_univ) hhi
      obtain ⟨h1, h2⟩ := hnum x hxx0 (addOrderOf (hp p)) L₂ (hPP p hpp) hn hL
      obtain ⟨i₀, _, _, hsum⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum A
        π (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (KE eps) (rE eps)
          (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
          (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU (dE eps x) := Nat.ceil_pos.mpr (by positivity)
      have h3 := UpperTheory.BernoulliSumsFrobeniusOrbits.not_good_le
        (fun i => π (bs (hp p) t + i • hp p)) (dE eps x)
        (addOrderOf (hp p)) L₂ (KE eps) (rE eps)
        (Formalism.MainNotions.G.goodU (dE eps x)) (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x)
        (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x)
        (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x) i₀ (fun i => hp1 _) hδ.le hδ1 hu h1
      refine le_trans (le_of_eq hsum) ?_
      rw [mul_comm (Cb * x ^ (-2 : ℝ))]
      exact le_trans (mul_le_mul_of_nonneg_left (h3.trans h2)
        (le_trans (by positivity) (hp1 t).1)) (mul_le_mul_of_nonneg_right (hp1 t).2 hβ))
    (Fintype.card_pos) S v σ hv hMass hσ
  exact ⟨T, by simpa using hT1 (), hT2, hT3⟩

set_option pp.fullNames true in
#print axioms goodWithSamplingProfile
end Uriel.OddPositions
