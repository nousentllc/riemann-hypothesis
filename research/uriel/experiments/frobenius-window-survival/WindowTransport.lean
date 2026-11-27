import NativeAccounting
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HC Formalism.MainNotions Formalism.L2.DIV
open Formalism.L2.GlobalTheoryTheory
open scoped BigOperators

namespace FrobeniusWindow
noncomputable section

theorem xprime_le_xdouble (s : Scale) (n : ℕ) (hn : 0 < n) :
    s.X' ≤ s.X'' n := by
  have hy : 0 < s.X' := Real.exp_pos _
  have hx : 1 ≤ s.x := s.one_lt_alt.le
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < s.a := mul_pos (by linarith) (Real.exp_pos _)
  have he : s.X'' n = s.X' * (s.x*n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [he]
  simpa using mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hx hn') hy.le

theorem noGain_false {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h : B.R.A} {p : ℕ} {Cr : ℝ}
    (hc : Arith.Loc.Cand B K h p) (hbig : B.sc.p0 B.R.k ≤ (p : ℝ))
    (hσ : Arith.Loc.Sig B I K a b h p ≤ B.sc.x^(-B.sc.eps)) (he : Even (addOrderOf h)) :
    ¬ Arith.Loc.NoGain B I K a b h p Cr := by
  have hnotBand := hc.2.2.2.2 hbig
  have hy : (p : ℝ) ≤ B.sc.X'' B.R.n := hc.2.1.le.trans (xprime_le_xdouble _ _ B.R.ord_pos)
  intro hn
  rcases hn with ⟨_,_,h1|⟨_,i,hi,ha⟩|⟨_,hs⟩⟩|h2|h3|⟨_,h4,_⟩
  · exact (not_lt_of_ge hc.2.2.2.1) h1
  · obtain ⟨h1,h2⟩ := abs_le.mp ha
    apply hnotBand
    refine ⟨hbig,hc.2.1,i,hi,?_,?_⟩
    · linarith only [h1]
    · linarith only [h2]
  · exact (not_lt_of_ge hσ) hs
  · exact (not_lt_of_ge hy) h2
  · exact h3 (Or.inl hc.2.2.1)
  · exact (Nat.not_odd_iff_even.mpr he) h4

theorem gainD_eq_native {N : NumDatum} {C : Arith.Cst} {Lv : Arith.Lev N} {p j : ℕ}
    (hc : Arith.Loc.Cand (Arith.base N) C.K (N.hP p) p)
    (hbig : N.sc.p0 N.R.k ≤ (p : ℝ))
    (hs : Arith.SigAt N C (Arith.aZ N) (Arith.bZ N) p ≤ N.sc.x^(-N.sc.eps))
    (he : Even (addOrderOf (N.hP p))) :
    Arith.gainD N C Lv p j =
      Arith.Loc.gainP (Arith.base N) (Arith.ins0 N C) C.K (Arith.aZ N) (Arith.bZ N)
        (N.hP p) p j (Arith.off N j) := by
  classical
  have hnd : p ∉ Arith.drop N C Lv := fun hd =>
    noGain_false hc hbig hs he hd.2.1
  rw [Arith.gainD,if_neg hnd]
  unfold Arith.gain Arith.gainAt
  rw [if_pos (Or.inl hc.2.2.1)]

theorem prime_in_support {N : NumDatum} (Lv : Arith.Lev N)
    {p : ℕ} (hp : p.Prime) (hy : (p : ℝ) < N.sc.X') : p ∈ Arith.suppP N Lv := by
  have ht : (p : ℝ) ≤ N.sc.X'' N.R.n := hy.le.trans (xprime_le_xdouble _ _ N.R.ord_pos)
  have hf : p ≤ ⌊N.sc.X'' N.R.n⌋₊ := Nat.le_floor ht
  unfold Arith.suppP NumDatum.suppP
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hf),hp⟩)))

section Place

variable {F : Type} [Field F] [NumberField F]

private theorem pOf_iff {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} (hp : p.Prime) :
    Arith.pOf w = p ↔ (p : 𝓞 F) ∈ w.asIdeal := by
  let : w.asIdeal.IsMaximal := w.isMaximal
  change ringChar ((𝓞 F) ⧸ w.asIdeal) = p ↔ _
  have he : (p : (𝓞 F) ⧸ w.asIdeal) = 0 ↔ (p : 𝓞 F) ∈ w.asIdeal := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal) (a := (p : 𝓞 F)))
  rw [← he]
  constructor
  · intro h
    rw [← h]
    exact CharP.cast_eq_zero _ _
  · intro h
    exact ((Nat.dvd_prime hp).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

theorem prime_fiber_weight (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ}
    (hp : p.Prime) (hS : ∀ w, Arith.pOf w = p → w ∈ S) :
    ∑ w ∈ S.filter (fun w => Arith.pOf w = p), lw F w * (eWL F w : ℝ) = Real.log p :=
  sum_lw_e p hp _ (fun w => ⟨fun hw => (pOf_iff hp).mp (Finset.mem_filter.mp hw).2,
    fun hm => by
      have he := (pOf_iff hp).mpr hm
      exact Finset.mem_filter.mpr ⟨hS w he,he⟩⟩)

private theorem support_prime {N : NumDatum} {Lv : Arith.Lev N}
    (hLv : Lv.admitted) {p : ℕ} (hp : p ∈ Arith.suppP N Lv) : p.Prime := by
  unfold Arith.suppP NumDatum.suppP at hp
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hp with hp|hp
      · exact (Finset.mem_filter.mp hp).2
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hp
        rcases hp with hp|hp|hp
        · exact hp ▸ N.g_prime 0
        · exact hp ▸ N.g_prime 1
        · exact hp ▸ N.hyp.2.1
    · obtain ⟨δ,hδ,rfl⟩ := Finset.mem_image.mp hp
      exact (hLv.1 δ hδ).1
  · exact Nat.prime_of_mem_primeFactors hp

theorem support_contains_fiber {N : NumDatum} {Lv : Arith.Lev N} (hLv : Lv.admitted)
    {p : ℕ} (hp : p ∈ Arith.suppP N Lv) (w : HeightOneSpectrum (𝓞 F))
    (hw : Arith.pOf w = p) : w ∈ Arith.supp N Lv F := by
  classical
  have has (q : ℕ) (hq : q.Prime) :
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∈ S ↔ Arith.pOf v = q := by
    obtain ⟨S,hS⟩ := finite_places_over (K := F) q hq
    exact ⟨S,fun v => (hS v).trans (pOf_iff hq).symm⟩
  let sets (q : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) :=
    if hq : q.Prime then Classical.choose (has q hq) else ∅
  let S := (Arith.suppP N Lv).biUnion sets
  have he (v : HeightOneSpectrum (𝓞 F)) : v ∈ S ↔ Arith.pOf v ∈ Arith.suppP N Lv := by
    unfold S
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨q,hq,hv⟩
      have hq' := support_prime hLv hq
      simp only [sets,dif_pos hq'] at hv
      exact ((Classical.choose_spec (has q hq') v).1 hv).symm ▸ hq
    · intro hv
      have hq' := support_prime hLv hv
      refine ⟨_,hv,?_⟩
      simp only [sets,dif_pos hq']
      exact (Classical.choose_spec (has (Arith.pOf v) hq') v).2 rfl
  have hfin : {v : HeightOneSpectrum (𝓞 F) | Arith.pOf v ∈ Arith.suppP N Lv}.Finite := by
    convert S.finite_toSet using 1
    ext v
    exact (he v).symm
  unfold Arith.supp
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  change Arith.pOf w ∈ Arith.suppP N Lv
  rwa [hw]

/-- Actual place weights give twice log p in Ga and once log p in IOsum. -/
theorem native_prime_buckets {N : NumDatum} {C : Arith.Cst} {Lv : Arith.Lev N}
    (hLv : Lv.admitted) {p : ℕ} (hp : p.Prime) (hy : (p : ℝ) < N.sc.X') :
    let S := (Arith.supp N Lv F).filter (fun w => Arith.pOf w = p)
    (∑ w ∈ S, Arith.sz w ((∑ j ∈ N.lifts, Arith.gainD N C Lv (Arith.pOf w) j) -
        Arith.tau N C (Arith.pOf w))) =
      2 * Real.log p * ((∑ j ∈ N.lifts, Arith.gainD N C Lv p j) - Arith.tau N C p) ∧
    (∑ w ∈ S, lw F w * (eWL F w : ℝ) * Arith.io N C (Arith.pOf w)) =
      Real.log p * Arith.io N C p := by
  intro S
  have hcoef := prime_fiber_weight (Arith.supp N Lv F) hp
    (fun w hw => support_contains_fiber hLv (prime_in_support Lv hp hy) w hw)
  change ∑ w ∈ S, lw F w * (eWL F w : ℝ) = _ at hcoef
  have hS (w : HeightOneSpectrum (𝓞 F)) (hw : w ∈ S) : Arith.pOf w = p :=
    (Finset.mem_filter.mp hw).2
  constructor
  · let r := (∑ j ∈ N.lifts, Arith.gainD N C Lv p j) - Arith.tau N C p
    calc
      _ = ∑ w ∈ S, (lw F w * (eWL F w : ℝ))*(2*r) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hS w hw]
        unfold Arith.sz r
        ring
      _ = _ := by rw [← Finset.sum_mul,hcoef]; unfold r; ring
  · calc
      _ = ∑ w ∈ S, lw F w * (eWL F w : ℝ) * Arith.io N C p := by
        exact Finset.sum_congr rfl (fun w hw => by rw [hS w hw])
      _ = _ := by rw [← Finset.sum_mul,hcoef]

/-- The same prime's native bucket retains the stipulated margin after
the full tau and the chosen interaction coefficient. -/
theorem window_margin {N : NumDatum} {C : Arith.Cst} {Lv : Arith.Lev N}
    (hLv : Lv.admitted) {p : ℕ}
    (hc : Arith.Loc.Cand (Arith.base N) C.K (N.hP p) p)
    (hbig : N.sc.p0 N.R.k ≤ (p : ℝ))
    (hσ : Arith.SigAt N C (Arith.aZ N) (Arith.bZ N) p ≤ N.sc.x^(-N.sc.eps))
    (he : Even (addOrderOf (N.hP p))) {ioWeight c : ℝ}
    (hnet : c ≤ primePremium (Arith.base N) (Arith.ins0 N C) C.K (Arith.aZ N) (Arith.bZ N)
      (N.hP p) p (Arith.off N) - Arith.tau N C p - ioWeight*Arith.io N C p) :
    let S := (Arith.supp N Lv F).filter (fun w => Arith.pOf w = p)
    let f := ∑ j ∈ N.lifts, fallback (Arith.base N) (Arith.ins0 N C) C.K
      (Arith.aZ N) (Arith.bZ N) (N.hP p) p j (Arith.off N j)
    2*Real.log p*(f+c) ≤
      (∑ w ∈ S, Arith.sz w ((∑ j ∈ N.lifts, Arith.gainD N C Lv (Arith.pOf w) j) -
        Arith.tau N C (Arith.pOf w))) -
      (2*ioWeight)*(∑ w ∈ S, lw F w*(eWL F w : ℝ)*Arith.io N C (Arith.pOf w)) := by
  intro S f
  obtain ⟨hg,hi⟩ := native_prime_buckets (F := F) (C := C) hLv hc.1 hc.2.1
  rw [hg,hi]
  have hzero : N.hP p ≠ 0 := by
    intro hh
    have hh' : addOrderOf (N.hP p) = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr hh
    rw [hh'] at he
    norm_num at he
  have hguard : ¬ (( (Arith.base N).IsResidueClassZero p ∧ N.hP p=0) ∨
      (Arith.base N).sc.X'' (Arith.base N).R.n < (p : ℝ)) :=
    not_or.mpr ⟨fun hh => hzero hh.2,
      not_lt_of_ge (hc.2.1.le.trans (xprime_le_xdouble _ _ N.R.ord_pos))⟩
  simp_rw [gainD_eq_native hc hbig hσ he]
  have heq := gain_lift_split (I := Arith.ins0 N C) (K := C.K) (a := Arith.aZ N)
    (b := Arith.bZ N) (off := Arith.off N) hguard
  change (∑ j ∈ N.lifts, Arith.Loc.gainP (Arith.base N) (Arith.ins0 N C) C.K
      (Arith.aZ N) (Arith.bZ N) (N.hP p) p j (Arith.off N j)) =
      f + primePremium (Arith.base N) (Arith.ins0 N C) C.K
        (Arith.aZ N) (Arith.bZ N) (N.hP p) p (Arith.off N) at heq
  rw [heq]
  have hlog : 0 ≤ 2*Real.log (p : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hc.1.one_le))
  have h := mul_le_mul_of_nonneg_left (add_le_add_left hnet f) hlog
  linarith only [h]

end Place
end
end FrobeniusWindow

#print axioms FrobeniusWindow.noGain_false
#print axioms FrobeniusWindow.gainD_eq_native
#print axioms FrobeniusWindow.support_contains_fiber
#print axioms FrobeniusWindow.native_prime_buckets

#print axioms FrobeniusWindow.window_margin
