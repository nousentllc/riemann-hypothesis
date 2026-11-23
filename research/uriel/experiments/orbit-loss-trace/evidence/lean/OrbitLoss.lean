import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

/-
Arithmetic orbit-loss audit. The low and global proofs adapt the pinned
LatticeChainSuccOfPartial.sum_low and latticeChain_succ_of_partial proofs.
Their other seven low-prime bounds and the original high-prime estimate
are preserved. Only the seventh term is delayed until the final comparison.
-/

/-- The source bad-charge functional vanishes if the canonical orbit of
each retained point at each prime in the actual filter is good. -/
theorem orbitLoss_BTT_zero (X : Inst D L)
    (good : ∀ p ∈ (primesResidueBelow D L.sc.X').filter (fun p =>
        L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ)),
      ∀ t ∈ D.host.TT, Good X p (X.bs (stepP D p) t)) :
    BTT D L X = 0 := by
  classical
  unfold BTT
  apply Finset.sum_eq_zero
  intro p hp
  have empty : D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨hm, hn⟩ := Finset.mem_filter.mp ht
    exact hn (good p hp t hm)
  simp [empty]

/-- Exact counterfactual at the summand of the source majorant. Only
the seventh summand reads the supplied bad-point count. -/
theorem orbitLoss_E1_difference (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ)
    (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) (p : ℕ) :
    E1 X K C bo a b A3 A4 PS badf p - E1 X K C bo a b A3 A4 PS (fun _ => 0) p =
      (if p ∈ PS then Real.log p / p * badf p else 0) * (3 * (D.R.m : ℝ) * L.sc.a) := by
  classical
  unfold E1
  by_cases hp : p ∈ PS <;> simp only [hp, if_true, if_false, mul_zero] <;> ring

/-- Before the numerical threshold replaces it by a fixed fraction of the
budget, the bad charge already has a vanishing relative cap for eps < 1. -/
theorem orbitLoss_relative (X : Inst D L) (h2 : adm2 D L X) :
    BTT D L X * (3 * (D.R.m : ℝ) * L.sc.a) ≤
    ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) *
      (3 * L.sc.x ^ (-1 + L.sc.eps)) := by
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hpow : L.sc.x ^ (-1 + L.sc.eps) =
      L.sc.x * L.sc.x ^ (-2 + L.sc.eps) := by
    calc L.sc.x ^ (-1 + L.sc.eps)
        = L.sc.x ^ ((1 : ℝ) + (-2 + L.sc.eps)) := by congr 1; ring
      _ = L.sc.x * L.sc.x ^ (-2 + L.sc.eps) := by rw [Real.rpow_add hx, Real.rpow_one]
  refine (mul_le_mul_of_nonneg_right h2.2 (by positivity : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a)).trans ?_
  apply le_of_eq
  rw [hpow]
  field_simp

theorem orbitLoss_low (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (hZZ : WReq X K a b) (N : PrimeSumNumericFacts D L K C bo)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      559 / 120 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) +
        (∑ p ∈ PS, Real.log p / p * badf p) * (3 * (D.R.m : ℝ) * L.sc.a) := by
  have ha := sc_one_lt_a L.sc
  have hx := sc_x_pos L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hA : 0 ≤ L.sc.a / L.sc.x := div_nonneg (by linarith) hx.le
  have hX'' : 0 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  have hc1 := first_constant_nonneg L C hC
  have hc2 := second_constant_nonneg L C hC
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hc4 := fourth_constant_nonneg K hK.1 L C hC
  have hcfl := cfl_nonneg D L.sc C hC
  refine le_trans (Finset.sum_le_sum (fun p hp =>
    low_le X K hK P C bo hC hbo h hG hSig T p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2)) ?_
  unfold E1
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have b1 : ∑ p ∈ S, (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    have := card_prB_le (L.sc.X'' D.R.n + 1) (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have b2 : ∑ p ∈ S, (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) ≤ Real.log 4 * L.sc.p0 D.R.k :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (p0_pos D L.sc).le)
  have b3 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p else 0) ≤ Real.log 4 * L.sc.X' :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (by have := one_le_X' L.sc; linarith))
  have b4 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p / p else 0) ≤ lX L.sc :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (sum_logdiv_prB _ (one_le_X' L.sc))
  have b5 : ∑ p ∈ S, (if p ∈ A3 then Real.log p / p else 0) ≤ 1 / L.sc.x / 120 :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s3 (rpow_le_inv_of_le_neg_two _ N.n5 _ (by unfold Formalism.MainNotions.G.hG; have := L.sc.eps_pos; linarith)))
  have b6 : ∑ p ∈ S, (if p ∈ A4 then Real.log p / p else 0) ≤ 1 / L.sc.x :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s4 (rpow_neg_le_inv _ _ le_rfl))
  have b7 : ∑ p ∈ S, (if p ∈ PS then Real.log p / p * badf p else 0) ≤
      ∑ p ∈ PS, Real.log p / p * badf p :=
    sum_ite_mem_le (fun p : ℕ => Real.log p / p * badf p)
      (fun p _ => mul_nonneg (lp_nonneg p) (T.hbad0 p))
  have b8 : ∑ p ∈ S, (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
      1 / L.sc.x / 120 := by
    refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
      (fun p hp => mul_nonneg (lp_nonneg p)
        (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
          (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
    exact le_trans ((WReq_iff X K a b).1 hZZ) (rpow_le_inv_of_le_neg_two L.sc N.n5 (-9) (by norm_num))
  have q1 := mul_bound b1 (add_nonneg (mul_nonneg hM hc1) (mul_nonneg hm hcfl))
    (R := 1 / 20 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n1 hM
      have e2 := mul_le_mul_of_nonneg_left N.n1' hm
      have e3 : (D.R.m : ℝ) * (L.sc.a / L.sc.x) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
        have := mul_le_mul_of_nonneg_left N.one_le_card_tops (mul_nonneg hm hA)
        nlinarith
      nlinarith)
  have q2 := mul_bound b2 (mul_nonneg hM hc2)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n2 hM
      linarith)
  have q3 := mul_bound b3 (mul_nonneg hM hc3)
    (R := 3 / 2 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n3 hM
      linarith)
  have q4 := mul_bound b4 (mul_nonneg hM hc4)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n4 hM
      linarith)
  have hMa : 0 ≤ 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by positivity
  have q5 := mul_bound b5 hMa
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q6 := mul_bound b6 hMa
    (R := 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q7 := mul_le_mul_of_nonneg_right b7 (by positivity : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a)
  have q8 := mul_bound b8 (by positivity : (0 : ℝ) ≤ 4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)
    (R := 1 / 30 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  linarith only [q1, q2, q3, q4, q5, q6, q7, q8]

theorem orbitLoss_global (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    (hG : GainBoundAll X K C bo) (hSig0 : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) (h2 : adm2 D L X) (h3 : adm3 D L)
    (h4 : ArchimedeanSignatureMatching D L K) (N : PrimeSumNumericFacts D L K C bo)
    {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) (hZZ : WReq X K a b)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ 281 / 60 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) + BTT D L X * (3 * (D.R.m : ℝ) * L.sc.a) := by
  classical
  have hW := inWin_of_box ha hb
  have hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p := fun p hp => hSig0 a b p hp
  have hXX := X'_le_X'' L.sc D.R.n (n_pos D)
  have h2' := h2.2
  unfold BTT at h2'
  unfold adm3 at h3
  have h4' := h4.2.2.2.2
  have T : Sets X K _ _ _ (fun p => ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)) :=
    { hA3 := fun p hp hc hX ho => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 (by linarith)), hp, by linarith, hc⟩, ho⟩
      hA4 := fun p hp hX hB => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hX), hp, hB⟩
      hPS := fun p hC => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hC.2.1), hC.1, hC.2.1, hC.2.2.1⟩, hC.2.2.2.1⟩
      hPSsub := fun p hp => by
          have h1 := (Finset.mem_filter.1 hp).1
          unfold primesResidueBelow at h1
          have h2 := (Finset.mem_filter.1 h1).2
          exact mem_prB.2 ⟨h2.1, h2.2.1⟩
      hbad := fun p _ => by
          have : (D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)) ⊆
              D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t)) := by
            intro t ht
            obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.1 ht
            refine Finset.mem_filter.2 ⟨ht1, fun hg => ht2 (Finset.mem_filter.2 ⟨ht1, ?_⟩)⟩
            unfold goodReps reps
            exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩
          exact_mod_cast Finset.card_le_card this
      hbad0 := fun p => Nat.cast_nonneg _
      s3 := h3
      s4 := h4'
      s2 := h2' }
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n)
    (fun p : ℕ => Real.log p * max 0 (Dfc X K a b p))
  have l1 := orbitLoss_low X K hK P C bo hC hbo hW (hG a b hW) hSig T hZZ N
    (S.filter (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n))
    (fun p hp => ⟨(hS p (Finset.mem_filter.1 hp).1).1, (hS p (Finset.mem_filter.1 hp).1).2, (Finset.mem_filter.1 hp).2⟩)
  have l2 := sum_high P X K C bo hW N (S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L.sc.X'' D.R.n))
    (fun p hp => not_le.1 (Finset.mem_filter.1 hp).2)
  unfold BTT
  linarith only [hsplit, l1, l2]

theorem orbitLoss_compare (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    (hG : GainBoundAll X K C bo) (hSig0 : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) (h2 : adm2 D L X) (h3 : adm3 D L)
    (h4 : ArchimedeanSignatureMatching D L K) (N : PrimeSumNumericFacts D L K C bo)
    {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) (hZZ : WReq X K a b)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p) :
    (∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ 113 / 24 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) ∧
    (BTT D L X = 0 → ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ 281 / 60 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) := by
  have split := orbitLoss_global X K hK P C bo hC hbo hG hSig0 h2 h3 h4 N ha hb hZZ S hS
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ D.host.TT.card := Nat.cast_nonneg _
  have ha0 := sc_one_lt_a L.sc
  have hcap := h2.2.trans (mul_le_mul_of_nonneg_left N.n7 ht)
  have hq := mul_bound hcap (by positivity : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  constructor
  · linarith only [split, hq]
  · intro zero
    simpa only [zero, zero_mul, add_zero] using split

set_option format.width 180

#print axioms orbitLoss_BTT_zero
#print axioms orbitLoss_E1_difference
#print axioms orbitLoss_relative
#print axioms orbitLoss_low
#print axioms orbitLoss_global
#print axioms orbitLoss_compare

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
