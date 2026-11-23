import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied

namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedPrimes

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

/-- One order constant precedes the choice of the window, the finite prime set,
and its classes. The two first-kind buckets are evaluated at unit multiplicities. -/
theorem first_reciprocal_budget :
    ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord →
      Windows P e K → LargeX P.x P.ε e K →
      ∀ (Ps : Finset ℕ) (cl : ℕ → PClass), (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) →
        FirstHyp P Ps cl →
        (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤
          sg P K / (2 * P.x) := by
  classical
  obtain ⟨C₁, hC₁⟩ := first_kind_bound
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  intro P e K hCord hW hL Ps cl hPs hF
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have first := first_le hC₁ (by rw [hCord]; exact le_max_left _ _) hW hL Ps cl hPs hF
    1 1 zero_le_one zero_le_one
  have ords := size_orders_bucket_bound P e K 1 1 hW hL zero_le_one le_rfl
  have band := size_band_bound P e K 1 1 hW hL zero_le_one le_rfl
  simp only [unitU, one_mul, mul_one] at first ords band
  rw [F.ha] at first
  apply (le_div_iff₀ (mul_pos (by norm_num) F.xpos)).2
  apply (mul_le_mul_iff_left₀ F.bpos).1
  linarith only [first, ords, band]

/-- The indicator and the positive signal in the original lhsW both pay
on every second-kind prime. This retains the threshold in the denominator. -/
theorem second_reciprocal_budget (Ps cand : Finset ℕ) (cl : ℕ → PClass)
    (θ R : ℝ) (Sig : ℕ → ℝ) (hθ : 0 ≤ θ)
    (hSig : ∀ p ∈ cand, 0 ≤ Sig p) (hW : lhsW cand θ Sig ≤ R)
    (hS : ∀ p ∈ Ps, cl p = PClass.second → p ∈ cand ∧ θ < Sig p) :
    (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤
      R / (2 + 4 * θ) := by
  classical
  apply (le_div_iff₀ (by positivity)).2
  rw [Finset.sum_mul]
  have hsub : Ps.filter (fun p => cl p = PClass.second) ⊆ cand := by
    intro p h
    exact (hS p (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2).1
  refine le_trans ?_ hW
  unfold lhsW
  refine le_trans (b := ∑ p ∈ Ps.filter (fun p => cl p = PClass.second),
    Real.log p / p * ((if θ < Sig p then (2 : ℝ) else 0) + 4 * Sig p))
    (Finset.sum_le_sum (fun p hp => ?_)) ?_
  · have h := (hS p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2).2
    exact mul_le_mul_of_nonneg_left
      (show 2 + 4 * θ ≤ (if θ < Sig p then (2 : ℝ) else 0) + 4 * Sig p by
        rw [if_pos h]; linarith) (logdiv_nonneg p)
  · apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have h := hSig p hp
    have : 0 ≤ (if θ < Sig p then (2 : ℝ) else 0) := by split_ifs <;> norm_num
    exact mul_nonneg (logdiv_nonneg p) (by linarith)

/-- Embed the loss support into the actual two disjoint source classes.
The cutoff converts the log-weight per prime into the reciprocal weight. -/
theorem dropped_log_budget (Ps D : Finset ℕ) (cl : ℕ → PClass) (Y u v : ℝ)
    (hsub : D ⊆ Ps) (hpr : ∀ p ∈ D, p.Prime)
    (hYp : ∀ p ∈ D, (p : ℝ) ≤ Y)
    (hD : ∀ p ∈ D, cl p = PClass.first ∨ cl p = PClass.second)
    (h1 : (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤ u)
    (h2 : (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤ v) :
    (∑ p ∈ D, Real.log p) / Y ≤ u + v := by
  classical
  rw [Finset.sum_div]
  have hweight : ∀ p ∈ D, Real.log p / Y ≤ Real.log p / p := by
    intro p hp
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
      (by exact_mod_cast (hpr p hp).pos) (hYp p hp)
  refine (Finset.sum_le_sum hweight).trans ?_
  have split := Finset.sum_filter_add_sum_filter_not D (fun p => cl p = PClass.first)
    (fun p : ℕ => Real.log p / p)
  rw [← split]
  apply add_le_add
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => logdiv_nonneg p)) h1
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hsub hp.1, hp.2⟩
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => logdiv_nonneg p)) h2
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hsub hp.1, (hD p hp.1).resolve_left hp.2⟩

/-- For any eligible subset covered by the first two source classes, bound its
normalized log sum directly with the two original budgets. -/
theorem combined_budget :
    ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord →
      Windows P e K → LargeX P.x P.ε e K →
      ∀ (Ps D cand : Finset ℕ) (cl : ℕ → PClass) (Sig : ℕ → ℝ),
        (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) → FirstHyp P Ps cl →
        (∀ p ∈ cand, 0 ≤ Sig p) → lhsW cand P.θ Sig ≤ (P.x ^ 9)⁻¹ →
        (∀ p ∈ Ps, cl p = PClass.second → p ∈ cand ∧ P.θ < Sig p) →
        D ⊆ Ps → (∀ p ∈ D, (p : ℝ) ≤ P.Xp) →
        (∀ p ∈ D, cl p = PClass.first ∨ cl p = PClass.second) →
        (∑ p ∈ D, Real.log p) / P.Xp ≤ sg P K / (2 * P.x) +
          (P.x ^ 9)⁻¹ / (2 + 4 * P.θ) := by
  obtain ⟨Cord, h0, hf⟩ := first_reciprocal_budget
  refine ⟨Cord, h0, ?_⟩
  intro P e K heq hW hL Ps D cand cl Sig hp hfirst hsig hbudget hsecond hsub hcut hD
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hθ : 0 ≤ P.θ := Real.rpow_nonneg F.xpos.le _
  exact dropped_log_budget Ps D cl P.Xp _ _ hsub (fun p h => (hp p (hsub h)).1)
    hcut hD (hf P e K heq hW hL Ps cl hp hfirst)
    (second_reciprocal_budget Ps cand cl P.θ _ Sig hθ hsig hbudget hsecond)

set_option pp.fullNames true
set_option format.width 200
#print axioms first_reciprocal_budget
#print axioms second_reciprocal_budget
#print axioms dropped_log_budget
#print axioms combined_budget
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedPrimes
