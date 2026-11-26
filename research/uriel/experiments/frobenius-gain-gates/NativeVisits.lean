import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

namespace FrobeniusGain
noncomputable section

private theorem reduced_nsmul_inj {A : Type*} [AddCommGroup A] {h : A} {i j : ℕ}
    (hi : i < addOrderOf h) (hj : j < addOrderOf h) (heq : i • h = j • h) : i = j := by
  have prohibit (a b : ℕ) (ha : a < addOrderOf h) (hab : b < a) (he : a • h = b • h) : False := by
    have hz : (a-b) • h = 0 := by
      apply add_right_cancel (b := b • h)
      rw [zero_add, ← add_nsmul, Nat.sub_add_cancel hab.le, he]
    have hd := addOrderOf_dvd_of_nsmul_eq_zero hz
    exact (not_le_of_gt (by omega : a-b < addOrderOf h)) (Nat.le_of_dvd (by omega) hd)
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt|hgt
  · exact prohibit j i hj hlt heq.symm
  · exact prohibit i j hi hgt heq

private theorem away_from_anchor {A : Type*} [AddCommGroup A] {h t : A} {i : ℕ}
    (hi : i < addOrderOf h) (h0 : 0 < i) : t + i • h ≠ t := by
  intro he
  have hz : i • h = 0 := add_left_cancel (show t + i • h = t+0 by simpa using he)
  exact h0.ne' (reduced_nsmul_inj hi (h0.trans hi) (by simpa using hz))

theorem inert_partner {B : Arith.Base} {p : ℕ} (hc : B.IsResidueClassZero p)
    (h t : B.R.A) (i : ℕ) :
    Arith.Loc.partner B h p t i = (false,t+i • h) := by
  have hs : ¬ B.IsSg p := by
    change ¬ B.cls p = .signal
    change B.cls p = .inertClass at hc
    rw [hc]
    decide
  simp [Arith.Loc.partner,hs]

theorem inert_step {B : Arith.Base} {p : ℕ} (hc : B.IsResidueClassZero p) (h : B.R.A) :
    Arith.Loc.stepP B h p = h := by
  have hs : ¬ B.IsSg p := by
    change ¬ B.cls p = .signal
    change B.cls p = .inertClass at hc
    rw [hc]
    decide
  simp [Arith.Loc.stepP,hs]

/-- In the reduced orbit, the actual native first-visit test is equivalent
to oddness and retention of the target. -/
theorem reduced_excl_iff {B : Arith.Base} {p : ℕ} (hc : B.IsResidueClassZero p)
    (h t : B.R.A) {e : ℕ} (he : e < addOrderOf h) :
    Arith.Loc.Excl B h p t e ↔ Odd e ∧ t+e • h ∈ B.TT := by
  constructor
  · rintro ⟨ho,t',ht',_,_,heq,_⟩
    rw [inert_partner hc] at heq
    have ht'' : t + e • h = t' := congrArg Prod.snd heq
    exact ⟨ho,ht'' ▸ ht'⟩
  · rintro ⟨ho,ht⟩
    refine ⟨ho,_,ht,away_from_anchor he ho.pos,ho.pos,inert_partner hc h t e,?_⟩
    intro j hj hjlt heq
    rw [inert_partner hc] at heq
    have eq' : j • h = e • h := add_left_cancel (congrArg Prod.snd heq)
    exact hjlt.ne (reduced_nsmul_inj (hjlt.trans he) he eq')

/-- Parity is relative to the literal orbit origin used in the consumer. -/
theorem isV_iff_even {B : Arith.Base} {I : Arith.Ins B} {p : ℕ}
    (hc : B.IsResidueClassZero p) {h t : B.R.A} {i : ℕ} (hi : i < addOrderOf h)
    (heq : I.bs h t + i • h = t) : Arith.Loc.IsV B I h p t ↔ Even i := by
  have hs : ¬ B.IsSg p := by
    change ¬ B.cls p = .signal
    change B.cls p = .inertClass at hc
    rw [hc]
    decide
  unfold Arith.Loc.IsV Arith.Loc.nP Arith.Loc.stepP
  simp only [if_neg hs]
  constructor
  · rintro ⟨k,hk,hke,ht⟩
    have hk' : k • h = i • h := add_left_cancel (ht.trans heq.symm)
    exact reduced_nsmul_inj hk hi hk' ▸ hke
  · exact fun h => ⟨i,hi,h,heq⟩

/-- Origins agree whenever two steps generate the same subgroup, so the
even child of the dyadic split is independent of the selected generator. -/
theorem origin_same_span {R : Ranks} {h k t : R.A}
    (hspan : AddSubgroup.zmultiples h = AddSubgroup.zmultiples k) :
    Arith.bsH h t = Arith.bsH k t := by
  classical
  have ex (v : ℕ) (g : R.A) :
      (∃ i : ℕ, R.ofNat v + i • g = t) ↔ t-R.ofNat v ∈ AddSubgroup.zmultiples g := by
    constructor
    · rintro ⟨i,hi⟩
      rw [← hi,add_sub_cancel_left]
      exact (AddSubgroup.zmultiples g).nsmul_mem (AddSubgroup.mem_zmultiples g) i
    · intro hh
      rw [mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hh
      obtain ⟨i,_,hi⟩ := hh
      exact ⟨i, by rw [hi]; abel⟩
  have iff' (v : ℕ) := (ex v h).trans (hspan ▸ (ex v k).symm)
  have hh : ∃ v : ℕ, ∃ i : ℕ, R.ofNat v+i • h=t := ⟨t.val,0,by simp⟩
  have hk : ∃ v : ℕ, ∃ i : ℕ, R.ofNat v+i • k=t := ⟨t.val,0,by simp⟩
  unfold Arith.bsH
  rw [dif_pos hh,dif_pos hk]
  congr 1
  exact Nat.find_congr' (fun {v} => iff' v)

/-- Apply the coefficient gate alone to a deep first visit. It is excluded
from the residual sum, and at an odd-origin anchor its minimum saturates
the geometric supply. The supply upper bound and retained capacity lower
bound are kept as explicit premises of the native calculation. -/
theorem deep_visit_accounting {B : Arith.Base} {I : Arith.Ins B}
    {a b : B.R.A → ℤ} {h t : B.R.A} {p j e : ℕ} {oj : Bool × B.R.A → ℝ}
    (hc : B.IsResidueClassZero p) (hp : 2 ≤ (p : ℝ))
    (he : e < addOrderOf h) (he3 : 3 ≤ e) (ho : Odd e)
    (ht : t+e • h ∈ B.TT) (hnV : ¬ Arith.Loc.IsV B I h p t)
    (hu : Arith.Loc.al B a t ≤ 2*B.sc.a)
    (hcap : B.sc.b' ≤ Arith.Loc.capU B b h p j oj t e)
    (hcubic : 2*B.sc.X' ≤ (p : ℝ)^3) :
    open Classical in
    (if Odd e ∧ ¬ Arith.Loc.Excl B h p t e then
      max 0 (Arith.Loc.al B a t/(p : ℝ)^e-Arith.Loc.capU B b h p j oj t e) else 0) = 0 ∧
    (if ¬ Arith.Loc.IsV B I h p t then
      (if Odd e then min (Arith.Loc.al B a t/(p : ℝ)^e)
        (Arith.Loc.capU B b h p j oj t e) else 0) else 0) =
      Arith.Loc.al B a t/(p : ℝ)^e := by
  classical
  have hex := (reduced_excl_iff hc h t he).2 ⟨ho,ht⟩
  have hy : 0 < B.sc.X' := Real.exp_pos _
  have ha : 0 < B.sc.a := mul_pos (by linarith [B.sc.one_lt_alt]) (Real.exp_pos _)
  have hb : 0 < B.sc.b' := div_pos ha hy
  have hs : B.sc.b' * B.sc.X' = B.sc.a := div_mul_cancel₀ _ hy.ne'
  have hd : 2*B.sc.X' ≤ (p : ℝ)^e := hcubic.trans (pow_le_pow_right₀ (by linarith) he3)
  have hb' := mul_le_mul_of_nonneg_left hd hb.le
  have hv : Arith.Loc.al B a t / (p : ℝ)^e ≤ B.sc.b' := by
    apply (div_le_iff₀ (pow_pos (by linarith) _)).2
    nlinarith only [hs,hb',hu]
  simp [hex,hnV,ho,min_eq_left (hv.trans hcap)]

end
end FrobeniusGain

#print axioms FrobeniusGain.reduced_excl_iff
#print axioms FrobeniusGain.isV_iff_even
#print axioms FrobeniusGain.origin_same_span
#print axioms FrobeniusGain.deep_visit_accounting
