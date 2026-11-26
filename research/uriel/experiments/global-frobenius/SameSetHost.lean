import HostArtin
import DyadicWitness

open Formalism.BasicNotions Formalism.HC Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

namespace GlobalFrobenius
noncomputable section

/-- Both correct old top partners of the same retained anchor, with reduced
    odd offsets and no alteration of the retained mask. -/
def TwoOdd {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  ∃ t : R.A, ∃ i j : ℕ, t ∈ H.TT ∧
    t + i • hPH H p ∈ H.TT ∧ t + j • hPH H p ∈ H.TT ∧
    Odd i ∧ Odd j ∧ i ≠ j ∧ i < addOrderOf (hPH H p) ∧ j < addOrderOf (hPH H p)

theorem original_partner_inert {R : Ranks} (s : Scale) (H : Host R) {p : ℕ}
    (hc : H.cls p = .inertClass) (t : R.A) (i : ℕ) :
    Arith.Loc.partner (baseOf s 0 0 H) (hPH H p) p t i =
      (false, t + i • hPH H p) := by
  have hn : ¬(baseOf s 0 0 H).IsSg p := by
    change ¬ H.cls p = .signal
    rw [hc]
    decide
  simp [Arith.Loc.partner, hn]

/-- The large coset is a filtered view of the existing set, not a new mask. -/
theorem host_step_two_odd {R : Ranks} (H : Host R) (k : ℕ) (hk : 2 ≤ k)
    (hcount : k * R.o < H.TT.card) :
    ∃ h t : R.A, ∃ i j : ℕ, k < addOrderOf h ∧
      t ∈ H.TT ∧ t + i • h ∈ H.TT ∧ t + j • h ∈ H.TT ∧
      Odd i ∧ Odd j ∧ i ≠ j ∧ i < addOrderOf h ∧ j < addOrderOf h := by
  classical
  have hcount' : k * R.toFrame.A0.index < H.TT.card := by
    rw [R.toFrame.index_A0_eq_o]
    exact hcount
  obtain ⟨c, hc⟩ := exists_coset_above R.toFrame.A0 H.TT k hcount'
  let F := H.TT.filter (fun t => (QuotientAddGroup.mk t : R.A ⧸ R.toFrame.A0) = c)
  have hF : k < F.card := hc
  have hcoset : ∀ a ∈ F, ∀ b ∈ F, b - a ∈ AddSubgroup.zmultiples R.toFrame.a0 := by
    intro a ha b hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact QuotientAddGroup.eq_iff_sub_mem.mp (hb'.trans ha'.symm)
  obtain ⟨h,t,i,j,hn,ht,hi,hj,oi,oj,hij,hil,hjl⟩ :=
    dyadic_coset_two_odd F R.toFrame.a0 R.toFrame.cyclic_order_dvd_two_pow
      (hk.trans_lt hF) hcoset
  exact ⟨h,t,i,j,hF.trans_le hn,(Finset.mem_filter.mp ht).1,
    (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hj).1,oi,oj,hij,hil,hjl⟩

/-- Any host with the requisite retained count already has real inert primes
    exhibiting a collision. No host fields or certificates need replacement. -/
theorem actual_mask_two_odd {R : Ranks} (H : Host R) (k lower : ℕ) (hk : 2 ≤ k)
    (hcount : k * R.o < H.TT.card) :
    ∃ p > lower, p.Prime ∧ H.cls p = .inertClass ∧ k < addOrderOf (hPH H p) ∧ TwoOdd H p := by
  obtain ⟨h,t,i,j,hn,ht,hi,hj,oi,oj,hij,hil,hjl⟩ := host_step_two_odd H k hk hcount
  obtain ⟨p,hp,hpr,hclass,heq⟩ := exists_inert_prime_step H h lower
  exact ⟨p,hp,hpr,hclass,heq.symm ▸ hn,by
    unfold TwoOdd
    rw [heq]
    exact ⟨t,i,j,ht,hi,hj,oi,oj,hij,hil,hjl⟩⟩

/-- Uniform lower bound from the actual retained-set and rank inequalities. -/
theorem retained_at_least_half_square {s : Scale} {R : Ranks} {H : Host R}
    {C8 : ℝ} (rv : RankVal s R) (hv : HostVal s C8 H) :
    s.x ^ 2 / 2 ≤ (H.TT.card : ℝ) := by
  have hx : 0 < s.x := zero_lt_one.trans s.one_lt_alt
  have hd : 0 ≤ s.delta1 := Real.rpow_nonneg hx.le _
  have hpow : s.x ^ 2 ≤ s.delta1 * (R.n : ℝ) := calc
    _ ≤ s.x ^ (2 + 8*s.eps - s.eps/8) := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos])
    _ = s.delta1 * s.x ^ (2 + 8*s.eps) := by
      unfold Scale.delta1
      rw [← Real.rpow_add hx]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left rv.n_lo hd
  linarith [hv.2.1.1]

theorem enough_for_long_order {s : Scale} {R : Ranks} {H : Host R}
    {C8 : ℝ} (rv : RankVal s R) (hv : HostVal s C8 H) (hx : 4*C8 < s.x) :
    (max 2 ⌈s.x ^ (s.eps/4)⌉₊) * R.o < H.TT.card := by
  have hX := s.one_lt_alt
  have hX0 : 0 < s.x := zero_lt_one.trans hX
  have hpow : s.x ^ (s.eps/4) ≤ s.x := calc
    _ ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (by linarith [s.eps_lt])
    _ = s.x := Real.rpow_one _
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hX0.le (s.eps/4))
  have hk : ((max 2 ⌈s.x ^ (s.eps/4)⌉₊ : ℕ) : ℝ) ≤ 2 * s.x := by
    push_cast
    exact max_le (by linarith) (by linarith)
  have hc' : (((max 2 ⌈s.x ^ (s.eps/4)⌉₊) * R.o : ℕ) : ℝ) < H.TT.card := calc
    _ ≤ (2 * s.x) * C8 := by
      rw [Nat.cast_mul]
      exact mul_le_mul hk hv.o_le (by positivity) (by positivity)
    _ < s.x ^ 2 / 2 := by nlinarith only [mul_lt_mul_of_pos_right hx hX0]
    _ ≤ _ := retained_at_least_half_square rv hv
  exact_mod_cast hc'

/-- Formal preservation of the entire host supply interface. Primes in this
    theorem can be chosen arbitrarily large. The cutoff theorem is separate. -/
theorem cofinal_original_hosts_two_odd {P : HostReq} (src : HostExP P)
    {eps : ℝ} (he : 0 < eps) (he' : eps < 1/52) (X : ℝ) (lower : ℕ) :
    ∃ (C8 C5 c6 Cb : ℝ) (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ),
      s.eps = eps ∧ X ≤ s.x ∧ RankVal s R ∧ HostGood s C8 C5 c6 Cb H q0 ∧
      P C5 s R H q0 ∧ ∃ p > lower, p.Prime ∧ H.cls p = .inertClass ∧
       s.x ^ (s.eps/4) ≤ (addOrderOf (hPH H p) : ℝ) ∧ TwoOdd H p := by
  obtain ⟨la,hla,h⟩ := src
  obtain ⟨CT2,C8,C5,c6,Cb,x0,_,_,_,_,S,hS⟩ := h eps he he'
  obtain ⟨s,hes,hxs,hm⟩ := S.exists_mem hla.le he he' (max X (max x0 (4*C8+1)))
  obtain ⟨R,H,q0,hr,hct,hg,hp⟩ := hS s hes (le_trans (le_max_left _ _) (le_of_max_le_right hxs)) hm
  have hx : 4*C8 < s.x := by
    have := (le_max_right x0 (4*C8+1)).trans (le_of_max_le_right hxs)
    linarith
  obtain ⟨p,hpl,hpp,hpc,ho,ht⟩ := actual_mask_two_odd H _ lower
    (le_max_left 2 _) (enough_for_long_order hr hg.1 hx)
  have hceil : ⌈s.x ^ (s.eps/4)⌉₊ ≤ addOrderOf (hPH H p) := (le_max_right 2 _).trans ho.le
  have heo : s.x ^ (s.eps/4) ≤ (addOrderOf (hPH H p) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  exact ⟨C8,C5,c6,Cb,s,R,H,q0,hes,le_of_max_le_left hxs,hr,hg,hp,p,hpl,hpp,hpc,heo,ht⟩

/-- The exact witness boundary for the strengthened selector. The field, ranks,
    twists and all set-independent arithmetic are preserved by the update. -/
theorem hostGood_of_new_retention {s : Scale} {R : Ranks} (H : Host R)
    {C8 C5 c6 Cb Cb' : ℝ} {q0 : ℕ} (old : HostGood s C8 C5 c6 Cb H q0)
    (T : Finset R.A)
    (low : s.delta1 * R.n / 2 ≤ (T.card : ℝ))
    (upper : (T.card : ℝ) ≤ 2 * s.delta1 * R.n)
    (score : BadOK s Cb' { H with TT := T }) :
    HostGood s C8 C5 c6 Cb' { H with TT := T } q0 := by
  rcases old with ⟨hv,ha,ht,hw,hq,hbox,hd,hthin,_,hr⟩
  rcases hv with ⟨hp,_,hv⟩
  exact ⟨⟨hp,⟨low,upper⟩,hv⟩,ha,ht,hw,hq,hbox,hd,hthin,score,hr⟩

end
end GlobalFrobenius

#print axioms GlobalFrobenius.original_partner_inert
#print axioms GlobalFrobenius.host_step_two_odd
#print axioms GlobalFrobenius.actual_mask_two_odd
#print axioms GlobalFrobenius.retained_at_least_half_square
#print axioms GlobalFrobenius.enough_for_long_order
#print axioms GlobalFrobenius.cofinal_original_hosts_two_odd
#print axioms GlobalFrobenius.hostGood_of_new_retention
