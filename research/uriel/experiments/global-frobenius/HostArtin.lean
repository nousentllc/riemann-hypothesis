import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.NumberTheory.LSeries.PrimesInAP

open NumberField Ideal Formalism.HC Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

namespace GlobalFrobenius
noncomputable section

/-- The exact class and chosen Frobenius coordinate of any prime in this unit class. -/
theorem inert_step_of_artin_class {R : Ranks} (H : Host R) (h : R.A)
    (u : (ZMod H.condN)ˣ) (hu : H.art u = (c0, R.iota h))
    {p : ℕ} (hp : p.Prime) (hr : (p : ZMod H.condN) = u) :
    H.cls p = .inertClass ∧ hPH H p = h := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hunit : IsUnit (p : ZMod H.condN) := hr.symm ▸ u.isUnit
  have hcop : p.Coprime H.condN := (ZMod.isUnit_iff_coprime _ _).mp hunit
  have hnd := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  let : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 H.E) (Ideal.span {(p : ℤ)})
  let : P.IsPrime := hP.isPrime
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hL
  obtain ⟨σ, hσ⟩ := (H.der.frob p hnd P).1
  have hg : H.galE σ = (c0, R.iota h) :=
    ((H.der.frob p hnd P).2.1 σ u hr.symm).mp hσ |>.trans hu
  refine ⟨(factClassFrob R H p hnd P σ hσ).2.2.mpr (congrArg Prod.fst hg), ?_⟩
  unfold hPH
  have hex : ∃ g : R.GG, g ∈ {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime)
      (_ : P.LiesOver (Ideal.span {(p : ℤ)})) (σ : H.E ≃ₐ[ℚ] H.E),
      IsArithFrobAt ℤ σ P ∧ H.galE σ = g} :=
    ⟨H.galE σ, P, hP.isPrime, hL, σ, hσ, rfl⟩
  obtain ⟨Q, hQ, hQo, τ, hτ, ht⟩ := Classical.epsilon_spec hex
  let : Q.IsPrime := hQ
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQo
  have hτ' := ((H.der.frob p hnd Q).2.1 τ u hr.symm).mp hτ
  change H.galE τ = H.art u at hτ'
  rw [← ht, hτ', hu]
  exact R.toFrame.iotaInv_iota h

/-- Prescribe the literal original inert Frobenius step on any fixed host.
    The result gives primes beyond every stated lower bound. -/
theorem exists_inert_prime_step {R : Ranks} (H : Host R) (h : R.A) (lower : ℕ) :
    ∃ p > lower, p.Prime ∧ H.cls p = .inertClass ∧ hPH H p = h := by
  obtain ⟨u, hu⟩ := H.der.art_surj (c0, R.iota h)
  obtain ⟨p, hlt, hp, hr⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit lower
  exact ⟨p, hlt, hp, inert_step_of_artin_class H h u hu hp hr⟩

end
end GlobalFrobenius

#print axioms GlobalFrobenius.inert_step_of_artin_class
#print axioms GlobalFrobenius.exists_inert_prime_step
