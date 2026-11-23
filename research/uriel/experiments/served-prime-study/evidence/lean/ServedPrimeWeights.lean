import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied

/-! Finite served-prime weight in the original discriminant-family loss hypotheses. -/

namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedWeights

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

variable {τ ι κ U : Type}

noncomputable def theta (S : Finset ℕ) : ℝ := ∑ p ∈ S, Real.log p

/-- The numerator of the effective log-weight; well defined even at zero retained cardinality. -/
noncomputable def servedNumerator (S : Finset ℕ) (TTp : ℕ → Finset τ) : ℝ :=
  ∑ p ∈ S, ((TTp p).card : ℝ) * Real.log p

/-- The exact shortfall in the numerator counts only omitted retained points. -/
theorem missing_identity (S : Finset ℕ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (sub : ∀ p ∈ S, TTp p ⊆ TT) :
    (TT.card : ℝ) * theta S - servedNumerator S TTp =
      ∑ p ∈ S, ((TT \ TTp p).card : ℝ) * Real.log p := by
  unfold theta servedNumerator
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hc : (((TT \ TTp p).card : ℕ) : ℝ) + ((TTp p).card : ℝ) = (TT.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (sub p hp)
  rw [← hc]
  ring

/-- Restricted support with arbitrary cap H. Only support primes must satisfy p ≤ H. -/
theorem capped_missing_weight (S PR : Finset ℕ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (BAD : ℕ → τ → Prop) (H : ℝ) (hH : 0 ≤ H)
    (hp : ∀ p ∈ S, 0 < p ∧ (p : ℝ) ≤ H) (sub : ∀ p ∈ S, TTp p ⊆ TT)
    (cov : ∀ p ∈ S, ∀ t ∈ TT \ TTp p, p ∈ PR ∧ BAD p t) :
    0 ≤ (TT.card : ℝ) * theta S - servedNumerator S TTp ∧
    (TT.card : ℝ) * theta S - servedNumerator S TTp ≤
      H * badPrimeLogWeightedCount PR TT BAD := by
  classical
  rw [missing_identity S TT TTp sub]
  constructor
  · exact Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
  · have mass := out_discriminant_bound τ S PR (fun _ => PClass.served) TT TTp BAD 1 1
        (badPrimeLogWeightedCount PR TT BAD) zero_le_one zero_le_one (le_refl _)
        (fun p h _ t ht => cov p h t ht)
    simp only [eq_self, Finset.filter_true, mul_one] at mass
    have cancel : (∑ p ∈ S, (Real.log p / p) * ((TT \ TTp p).card : ℝ)) ≤
        badPrimeLogWeightedCount PR TT BAD := by
      have eq : (∑ p ∈ S, 4 * (Real.log p / p) * ((TT \ TTp p).card : ℝ)) =
          4 * (∑ p ∈ S, (Real.log p / p) * ((TT \ TTp p).card : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith only [eq, mass]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left cancel hH)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p h => ?_)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hp p h).1
    have w := logdiv_nonneg p
    have p_le := mul_le_mul_of_nonneg_right (hp p h).2
      (mul_nonneg w (Nat.cast_nonneg (TT \ TTp p).card))
    have e : (p : ℝ) * (Real.log p / p * ((TT \ TTp p).card : ℝ)) =
        ((TT \ TTp p).card : ℝ) * Real.log p := by field_simp
    linarith only [e, p_le]

/-- The original data provide positivity of primes, TTp ⊆ TT and failure coverage. -/
theorem family_weight (P : Par) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ)
    (hyp : PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D)
    (u : U) (S : Finset ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hS : ∀ p ∈ S, p ∈ Ps ∧ (D u).cl p = PClass.served ∧ (p : ℝ) ≤ H) :
    0 ≤ (TT.card : ℝ) * theta S - servedNumerator S (D u).TTp ∧
    (TT.card : ℝ) * theta S - servedNumerator S (D u).TTp ≤
      H * badPrimeLogWeightedCount PR TT BAD := by
  obtain ⟨_, hpr, _, _, _, _, hAll⟩ := hyp
  obtain ⟨hPar, _, _, hcov⟩ := hAll u
  obtain ⟨_, _, _, _, _, _, hSize, _⟩ := hPar
  apply capped_missing_weight S PR TT (D u).TTp BAD H hH
  · intro p hp
    exact ⟨(hpr p (hS p hp).1).1.pos, (hS p hp).2.2⟩
  · intro p hp
    exact (hSize p (hS p hp).1 (hS p hp).2.1).1
  · intro p hp
    exact hcov p (hS p hp).1 (hS p hp).2.1

theorem family_normalized (P : Par) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ)
    (hyp : PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D)
    (u : U) (S : Finset ℕ) (H : ℝ) (hH : 0 < H)
    (hS : ∀ p ∈ S, p ∈ Ps ∧ (D u).cl p = PClass.served ∧ (p : ℝ) ≤ H) :
    0 ≤ (theta S - servedNumerator S (D u).TTp / TT.card) / H ∧
    (theta S - servedNumerator S (D u).TTp / TT.card) / H ≤ P.x ^ (-2 + P.ε) := by
  have ht : (0 : ℝ) < TT.card := by exact_mod_cast Finset.card_pos.mpr hyp.1
  obtain ⟨nonneg, bound⟩ := family_weight P Ps cand PR J TT BAD Sig io D hyp u S H hH.le hS
  have hmass := hyp.2.2.2.2.1
  have e : (theta S - servedNumerator S (D u).TTp / TT.card) / H =
      ((TT.card : ℝ) * theta S - servedNumerator S (D u).TTp) / (H * TT.card) := by
    field_simp
  rw [e]
  refine ⟨div_nonneg nonneg (mul_pos hH ht).le, (div_le_iff₀ (mul_pos hH ht)).2 ?_⟩
  have last := mul_le_mul_of_nonneg_left hmass hH.le
  linarith only [bound, last]

theorem zero_mass_exact (S PR : Finset ℕ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (BAD : ℕ → τ → Prop) (H : ℝ) (hH : 0 ≤ H)
    (hp : ∀ p ∈ S, 0 < p ∧ (p : ℝ) ≤ H) (sub : ∀ p ∈ S, TTp p ⊆ TT)
    (cov : ∀ p ∈ S, ∀ t ∈ TT \ TTp p, p ∈ PR ∧ BAD p t)
    (zero : badPrimeLogWeightedCount PR TT BAD = 0) :
    (TT.card : ℝ) * theta S = servedNumerator S TTp := by
  obtain ⟨hn, hb⟩ := capped_missing_weight S PR TT TTp BAD H hH hp sub cov
  rw [zero, mul_zero] at hb
  linarith

/-- Partition the entire inert prime band I into dropped and surviving prime supports. -/
theorem split_drop (I drop : Finset ℕ) :
    theta I = theta (I \ drop) + theta (I ∩ drop) := by
  unfold theta
  exact (Finset.sum_inter_add_sum_sdiff I drop (fun p : ℕ => Real.log p)).symm.trans (add_comm _ _)

/-- The ordering cutoff plus the total reciprocal-weight of drops bounds their log-weight. -/
theorem drop_weight_bound (I drop : Finset ℕ) (H : ℝ)
    (hcap : ∀ p ∈ I ∩ drop, 0 < p ∧ (p : ℝ) ≤ H) :
    theta I - theta (I \ drop) ≤ H * ∑ p ∈ I ∩ drop, Real.log p / p := by
  rw [split_drop I drop, add_sub_cancel_left]
  unfold theta
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hcap p hp).1
  have h := mul_le_mul_of_nonneg_right (hcap p hp).2 (logdiv_nonneg p)
  have eq : (p : ℝ) * (Real.log p / p) = Real.log p := by field_simp
  linarith only [eq, h]

/-- Exact cost of the C b'/x part of the local allowance before replacing
served cardinalities or bounding the prime log-sum. -/
theorem leading_cost (P : Par) (m : ℝ) (S : Finset ℕ) (TT : Finset τ)
    (TTp : ℕ → Finset τ) (hx : 0 < P.x) (ht : 0 < TT.card) :
    (∑ p ∈ S, 2 * Real.log p * m * (TTp p).card * (P.C * (P.bp / P.x))) =
    2 * P.C * unitU P m TT.card * (servedNumerator S TTp / TT.card) / P.Xp := by
  have hx' : P.x ≠ 0 := hx.ne'
  have ht' : (TT.card : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hXp : P.Xp ≠ 0 := (Real.exp_pos _).ne'
  have hbp : P.bp / P.x = P.b / P.Xp := by
    change (P.x * P.b / P.Xp) / P.x = P.b / P.Xp
    field_simp
  have e : (∑ p ∈ S, 2 * Real.log p * m * (TTp p).card * (P.C * (P.bp / P.x))) =
      (2 * m * (P.C * (P.bp / P.x))) * servedNumerator S TTp := by
    unfold servedNumerator
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [e, hbp]
  unfold unitU
  field_simp

/-- The omitted support and the point-count shortfall are separate additive costs.
The drop estimate may be supplied by the source's independent prime class bounds. -/
theorem family_complete_band (P : Par) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ)
    (hyp : PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D)
    (u : U) (I drop : Finset ℕ) (H R : ℝ) (hH : 0 < H)
    (hI : ∀ p ∈ I, p ∈ Ps ∧ (p : ℝ) ≤ H)
    (hs : ∀ p ∈ I \ drop, (D u).cl p = PClass.served)
    (hDrop : (∑ p ∈ I ∩ drop, Real.log p / p) ≤ R) :
    0 ≤ (theta I - servedNumerator (I \ drop) (D u).TTp / TT.card) / H ∧
    (theta I - servedNumerator (I \ drop) (D u).TTp / TT.card) / H ≤ R + P.x ^ (-2 + P.ε) := by
  have h := family_normalized P Ps cand PR J TT BAD Sig io D hyp u (I \ drop) H hH (by
    intro p hp
    have hi := hI p (Finset.mem_sdiff.mp hp).1
    exact ⟨hi.1, hs p hp, hi.2⟩)
  have dropcap := drop_weight_bound I drop H (by
    intro p hp
    have hi := hI p (Finset.mem_inter.mp hp).1
    exact ⟨(hyp.2.1 p hi.1).1.pos, hi.2⟩)
  have small : (theta I - theta (I \ drop)) / H ≤ R := by
    apply (div_le_iff₀ hH).mpr
    linarith only [dropcap.trans (mul_le_mul_of_nonneg_left hDrop hH.le)]
  have pos : 0 ≤ (theta I - theta (I \ drop)) / H := by
    rw [split_drop I drop, add_sub_cancel_left]
    exact div_nonneg (Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)) hH.le
  have eq : (theta I - servedNumerator (I \ drop) (D u).TTp / TT.card) / H =
      (theta I - theta (I \ drop)) / H +
        (theta (I \ drop) - servedNumerator (I \ drop) (D u).TTp / TT.card) / H := by ring
  rw [eq]
  exact ⟨add_nonneg pos h.1, add_le_add small h.2⟩

set_option pp.fullNames true

#print axioms missing_identity
#print axioms capped_missing_weight
#print axioms family_weight
#print axioms family_normalized
#print axioms zero_mass_exact
#print axioms split_drop
#print axioms drop_weight_bound
#print axioms leading_cost
#print axioms family_complete_band

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedWeights
