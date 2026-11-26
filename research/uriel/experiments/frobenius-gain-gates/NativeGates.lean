import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX
open scoped BigOperators

namespace FrobeniusGain
noncomputable section

/-- The full interval is clear of every forbidden prime power:
degree one is below the band; all higher degrees are above it. -/
theorem outside_power_band {B : Arith.Base} {K : G.Consts} {p : ℕ}
    (hp : 1 ≤ (p : ℝ)) (hρ : B.rhoB K < 1/2)
    (hpLo : (3/2) * B.sc.X' < (p : ℝ)^2) (hpHi : (p : ℝ) < B.sc.X'/2) :
    ¬ B.InBand K p := by
  rintro ⟨_,_,i,hi,hl,hu⟩
  have hy : 0 < B.sc.X' := Real.exp_pos _
  by_cases h : i = 1
  · subst i
    simp only [pow_one] at hl
    nlinarith only [hl,hpHi,hρ, mul_pos hy (sub_pos.mpr hρ)]
  · have hh : (p : ℝ)^2 ≤ (p : ℝ)^i := pow_le_pow_right₀ hp (by omega)
    nlinarith only [hpLo,hu,hh,hρ, mul_pos hy (sub_pos.mpr hρ)]

theorem candidate_of_interior {B : Arith.Base} {K : G.Consts} {p : ℕ} {h : B.R.A}
    (hp : p.Prime) (hc : B.IsResidueClassZero p)
    (horder : B.sc.x ^ (B.sc.eps/4) ≤ (addOrderOf h : ℝ))
    (hρ : B.rhoB K < 1/2) (hpLo : (3/2)*B.sc.X' < (p : ℝ)^2)
    (hpHi : (p : ℝ) < B.sc.X'/2) : Arith.Loc.Cand B K h p := by
  refine ⟨hp, ?_, hc, horder, fun _ => outside_power_band (by exact_mod_cast hp.one_le) hρ hpLo hpHi⟩
  have hy : 0 < B.sc.X' := Real.exp_pos _
  linarith

theorem capacity_nonneg (B : Arith.Base) (K : G.Consts) (hk : 0 ≤ K.kII)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) (t : B.R.A) :
    0 ≤ Arith.Loc.kapv B (Arith.ins B K 1) K a b h p t := by
  unfold Arith.Loc.kapv Arith.Loc.kapLoc
  split_ifs
  · unfold Arith.Loc.kapIIf
    exact le_min zero_le_one (mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hk (by positivity)) (sq_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by linarith [B.sc.one_lt_alt]) _))
  · change 0 ≤ sInf _
    exact Real.sInf_nonneg fun κ hc => hc.1

theorem sig_nonneg (B : Arith.Base) (K : G.Consts) (hk : 0 ≤ K.kII)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) :
    0 ≤ Arith.Loc.Sig B (Arith.ins B K 1) K a b h p := by
  unfold Arith.Loc.Sig
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => capacity_nonneg B K hk a b h p t)

/-- The rejection indicator already appears in the original weight budget.
The total prime weight of capacity failures is at most half that budget. -/
theorem wok_rejection_weight {R : Ranks} (s : Scale) (H : Host R) (K : G.Consts)
    (a b : R.A → ℤ) (cD ch : ℝ) (hk : 0 ≤ K.kII)
    (hW : WOK s cD ch K H a b) :
    let B := baseOf s cD ch H
    let cand := fun p => Arith.Loc.Cand B K (hPH H p) p
    let sig := fun p => Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p
    open Classical in
    (∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => cand p ∧ s.x^(-s.eps) < sig p),
        Real.log p / p) ≤ s.x ^ (-9 : ℝ) / 2 := by
  classical
  dsimp only
  let B := baseOf s cD ch H
  let P := (Finset.range ⌈s.X'⌉₊).filter (fun p => Arith.Loc.Cand B K (hPH H p) p)
  let v := fun p => Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p
  let fail := fun p => s.x^(-s.eps) < v p
  have heq : P.filter fail = (Finset.range ⌈s.X'⌉₊).filter (fun p =>
      Arith.Loc.Cand B K (hPH H p) p ∧ fail p) := by
    simp [P, Finset.filter_filter]
  rw [← heq]
  change ∑ p ∈ P, Real.log p / p * (2 * (if fail p then (1 : ℝ) else 0) + 4 * v p) ≤ _ at hW
  have term (p : ℕ) (hp : p ∈ P) :
      2 * (if fail p then Real.log p / p else 0) ≤
      Real.log p / p * (2 * (if fail p then (1 : ℝ) else 0) + 4 * v p) := by
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hw : 0 ≤ Real.log (p : ℝ) / p :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (by positivity)
    have hσ := sig_nonneg B K hk a b (hPH H p) p
    have hv : 0 ≤ Real.log (p : ℝ) / p * (4*v p) :=
      mul_nonneg hw (mul_nonneg (by norm_num) hσ)
    by_cases hf : fail p
    · simp [hf]; nlinarith only [hv]
    · simpa [hf] using hv
  have hs := Finset.sum_le_sum term
  rw [← Finset.mul_sum, ← Finset.sum_filter] at hs
  linarith only [hs.trans hW]

theorem mem_vv_of_good {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h t : B.R.A} {p : ℕ}
    (hc : Arith.Loc.Cand B K h p)
    (hs : Arith.Loc.Sig B I K a b h p ≤ B.sc.x ^ (-B.sc.eps))
    (hg : Arith.Loc.Good B h (I.bs (Arith.Loc.stepP B h p) t)) :
    I.bs (Arith.Loc.stepP B h p) t ∈ Arith.Loc.VV B I K a b h p := by
  classical
  rw [Arith.Loc.VV,if_pos ⟨hc,hs⟩,Arith.Loc.goodReps,Finset.mem_filter]
  exact ⟨Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩,hg⟩

end
end FrobeniusGain

#print axioms FrobeniusGain.candidate_of_interior
#print axioms FrobeniusGain.wok_rejection_weight
#print axioms FrobeniusGain.mem_vv_of_good
