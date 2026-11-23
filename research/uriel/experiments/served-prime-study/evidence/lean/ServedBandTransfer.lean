import ServedPrimeWeights
import DroppedPrimeCosts

/-! Combine the actual family hypotheses with the first- and second-prime costs. -/

namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedBand

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedWeights

noncomputable def errorBudget (P : Par) (K : ℝ) : ℝ :=
  sg P K / (2 * P.x) + (P.x ^ 9)⁻¹ / (2 + 4 * P.θ) + P.x ^ (-2 + P.ε)

/-- I can be any subset of the input primes below X'. In particular one may impose
the inert class and lower cutoff before measuring which primes are served. -/
theorem complete_comparison :
    ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord →
      Windows P e K → LargeX P.x P.ε e K →
      ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
        (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
        PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D →
        ∀ (u : U) (I : Finset ℕ), (∀ p ∈ I, p ∈ Ps ∧ (p : ℝ) ≤ P.Xp) →
        let S := I.filter (fun p => (D u).cl p = PClass.served)
        0 ≤ (theta I - servedNumerator S (D u).TTp / TT.card) / P.Xp ∧
        (theta I - servedNumerator S (D u).TTp / TT.card) / P.Xp ≤ errorBudget P K := by
  obtain ⟨Cord, hn, budget⟩ := ServedPrimes.combined_budget
  refine ⟨Cord, hn, ?_⟩
  intro P e K hc hw hL ι κ τ U Ps cand PR J TT BAD Sig io D hyp u I hI
  dsimp only
  have joint := hyp
  obtain ⟨_, hp, hsig, hws, _, _, hAll⟩ := joint
  obtain ⟨hPar, hFirst, hSecond, _⟩ := hAll u
  obtain ⟨_, _, _, _, _, high, _⟩ := hPar
  obtain ⟨z, u0, E, X, sb1, sb2, v, w, F⟩ := facts hw hL
  have hXp : 0 < P.Xp := by rw [F.hXp]; exact F.Xpos
  have hcut : P.Xp ≤ P.Xpp := by
    rw [F.hXp, F.hXpp]
    exact le_mul_of_one_le_left F.Xpos.le (one_le_mul_of_one_le_of_one_le F.x1 F.n1)
  let S := I.filter (fun p => (D u).cl p = PClass.served)
  let Z := I.filter (fun p => ¬ (D u).cl p = PClass.served)
  have first_or_second : ∀ p ∈ Z, (D u).cl p = PClass.first ∨ (D u).cl p = PClass.second := by
    intro p hpZ
    obtain ⟨hi, hn⟩ := Finset.mem_filter.mp hpZ
    have := hI p hi
    cases val : (D u).cl p with
    | served => exact (hn val).elim
    | first => exact Or.inl rfl
    | second => exact Or.inr rfl
    | high => exact ((not_lt_of_ge (this.2.trans hcut)) (high p this.1 val)).elim
  have dz := budget P e K hc hw hL Ps Z cand (D u).cl Sig hp hFirst hsig hws hSecond
    (fun p h => (hI p (Finset.mem_filter.mp h).1).1)
    (fun p h => (hI p (Finset.mem_filter.mp h).1).2) first_or_second
  change theta Z / P.Xp ≤ _ at dz
  have sn := family_normalized P Ps cand PR J TT BAD Sig io D hyp u S P.Xp hXp (by
    intro p h
    obtain ⟨hi, hs⟩ := Finset.mem_filter.mp h
    exact ⟨(hI p hi).1, hs, (hI p hi).2⟩)
  have partition : theta S + theta Z = theta I :=
    Finset.sum_filter_add_sum_filter_not I (fun p => (D u).cl p = PClass.served) (fun p => Real.log p)
  have both : (theta I - servedNumerator S (D u).TTp / TT.card) / P.Xp =
      theta Z / P.Xp + (theta S - servedNumerator S (D u).TTp / TT.card) / P.Xp := by
    rw [← partition]; ring
  change 0 ≤ (theta I - servedNumerator S (D u).TTp / TT.card) / P.Xp ∧
    (theta I - servedNumerator S (D u).TTp / TT.card) / P.Xp ≤ errorBudget P K
  rw [both]
  have dz0 : 0 ≤ theta Z / P.Xp := div_nonneg (Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)) hXp.le
  exact ⟨add_nonneg dz0 sn.1, add_le_add dz sn.2⟩

/-- Allow an independently supplied estimate for the normalized inert prime count.
The interval is one-sided in the amount lost by service. -/
theorem target_transfer (total effective target width loss : ℝ)
    (estimate : |total - target| ≤ width)
    (service : 0 ≤ total - effective ∧ total - effective ≤ loss) :
    target - width - loss ≤ effective ∧ effective ≤ target + width := by
  obtain ⟨hl, hu⟩ := abs_le.mp estimate
  constructor <;> linarith only [hl, hu, service.1, service.2]

set_option pp.fullNames true
#print axioms complete_comparison
#print axioms target_transfer

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.ServedBand
