import SameSetHost
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty

open Real Filter NumberField Formalism.BasicNotions Formalism.HC GlobalTheory.EX

namespace GlobalFrobenius
noncomputable section

/-- The conductor exponent eps/5 leaves a strict margin at the prime cutoff
    with exponent eps/3, for any uniform polynomial least-prime bound. -/
theorem polynomial_room {eps C L : ℝ} (he : 0 < eps) (hC : 0 < C) (hL : 0 < L) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, 0 < N →
      Real.log (N : ℝ) ≤ 2 * x ^ (eps/5) * Real.log x ^ 2 →
      C * (N : ℝ) ^ L < Real.exp (x ^ (eps/3)) := by
  have ha : 0 < 2*eps/15 := by linarith
  have hb := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).bound
    (show 0 < 1/(4*L) by positivity)
  have hc := (tendsto_rpow_atTop (show 0 < eps/3 by linarith)).eventually_ge_atTop (4*Real.log C)
  filter_upwards [hb, hc, eventually_ge_atTop (1 : ℝ)] with x hb hc hx N hn hcond
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hN : (0:ℝ) < N := by exact_mod_cast hn
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hb
  have e1 : 2 * x ^ (eps/5) * Real.log x ^ 2 * L ≤ x ^ (eps/3) / 2 := calc
    _ ≤ 2 * x ^ (eps/5) * (1/(4*L) * x ^ (2*eps/15)) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hL.le
    _ = (x ^ (eps/5) * x ^ (2*eps/15)) / 2 := by field_simp; ring
    _ = _ := by rw [← Real.rpow_add hx0, show eps/5+2*eps/15 = eps/3 by ring]
  have hE : 0 < x ^ (eps/3) := Real.rpow_pos_of_pos hx0 _
  apply (Real.log_lt_log_iff (by positivity) (Real.exp_pos _)).mp
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hN _).ne',
    Real.log_rpow hN, Real.log_exp]
  have hyp := (mul_le_mul_of_nonneg_right hcond hL.le).trans e1
  linarith

/-- Only the exact upstream least-prime interface is needed; application to
    the chosen Artin class is independent of the choice of the retained set. -/
theorem bounded_inert_step {C L : ℝ}
    (bound : ∀ a q : ℕ, 1 ≤ a → 1 ≤ q → a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L)
    {R : Ranks} (H : Host R) (h : R.A) :
    ∃ p, p.Prime ∧ H.cls p = .inertClass ∧ hPH H p = h ∧
      (p : ℝ) ≤ C * (H.condN : ℝ) ^ L := by
  obtain ⟨u,hu⟩ := H.der.art_surj (Formalism.FrobeniusOrbits.c0,R.iota h)
  let a := (u : ZMod H.condN).val + H.condN
  have hn : 1 ≤ H.condN := H.condN_pos
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hv : (a : ZMod H.condN) = u := by simp [a]
  have hcop : a.Coprime H.condN := (ZMod.isUnit_iff_coprime _ _).mp (hv.symm ▸ u.isUnit)
  obtain ⟨p,hp,hpa,hpL⟩ := bound a H.condN ha hn hcop
  have hr := (ZMod.natCast_eq_natCast_iff p a H.condN).mpr hpa |>.trans hv
  exact ⟨p,hp,(inert_step_of_artin_class H h u hu hp hr).1,
    (inert_step_of_artin_class H h u hu hp hr).2,hpL⟩

/-- A same-set collision below the original selector cutoff, including the
    original threshold on the order of the Frobenius step. -/
theorem cofinal_below_cutoff {P : HostReq} (src : HostExP P)
    (linnik : GlobalTheory.Published.Linnik)
    {eps : ℝ} (he : 0 < eps) (he' : eps < 1/52) (X : ℝ) :
    ∃ (C8 C5 c6 Cb : ℝ) (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ),
      s.eps = eps ∧ X ≤ s.x ∧ RankVal s R ∧ HostGood s C8 C5 c6 Cb H q0 ∧
      P C5 s R H q0 ∧ ∃ p : ℕ, p.Prime ∧ (p : ℝ) < s.X' ∧ H.cls p = .inertClass ∧
        s.x ^ (s.eps/4) ≤ (addOrderOf (hPH H p) : ℝ) ∧ TwoOdd H p := by
  obtain ⟨C,L,hC,hL,hLP⟩ := GlobalTheory.Published.linnik_iff_exists_prime.mp linnik
  obtain ⟨xmin, hmin⟩ := eventually_atTop.mp (polynomial_room he hC hL)
  obtain ⟨C8,C5,c6,Cb,s,R,H,q0,hes,hX,hr,hH,hP,p,_,_,_,horder,ht⟩ :=
    cofinal_original_hosts_two_odd src he he' (max xmin X) 0
  obtain ⟨p',hp',hclass,hstep,hbound⟩ := bounded_inert_step hLP H (hPH H p)
  have hlog : Real.log (H.condN : ℝ) ≤ 2 * s.x ^ (eps/5) * Real.log s.x ^ 2 := by
    simpa [← hes, Formalism.HC.HostRaw.condN] using hH.1.log_cond_le
  have room := hmin s.x (le_of_max_le_left hX) H.condN H.condN_pos hlog
  have hcut : (p' : ℝ) < s.X' := by
    unfold Scale.X'
    rw [hes]
    exact hbound.trans_lt room
  have horder' : s.x ^ (s.eps/4) ≤ (addOrderOf (hPH H p') : ℝ) := by simpa [hstep] using horder
  have ht' : TwoOdd H p' := by simpa [TwoOdd,hstep] using ht
  exact ⟨C8,C5,c6,Cb,s,R,H,q0,hes,le_of_max_le_right hX,hr,hH,hP,p',hp',hcut,hclass,horder',ht'⟩

end
end GlobalFrobenius

#print axioms GlobalFrobenius.polynomial_room
#print axioms GlobalFrobenius.bounded_inert_step
#print axioms GlobalFrobenius.cofinal_below_cutoff
