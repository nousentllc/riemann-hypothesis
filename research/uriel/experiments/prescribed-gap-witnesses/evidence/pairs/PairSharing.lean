import Development.AutomorphicArithmetic.CharacterBoxes.PairGood

open Filter Set Formalism.HC UpperTheory.Top
open scoped Topology

namespace SuccessivePairs

noncomputable def z (eps Y : ℝ) := Y^(eps/5)
noncomputable def h (eps Y : ℝ) := z eps Y * (Real.log Y)^2
noncomputable def nextInt (a : ℝ) : ℝ := (⌊a⌋₊ : ℝ) + 1

/-- All tests concern the predetermined scales, and none mention either selected prime. -/
def Guard (M : ℕ) (eps J Y V : ℝ) : Prop :=
  z eps V < nextInt (z eps Y) ∧
  Real.exp (z eps V / 2) < nextInt (Real.exp (z eps Y / 2)) ∧
  Real.exp (h eps V / 2) < nextInt (Real.exp (h eps Y / 2)) ∧
  (∀ j : Fin 2, height M eps V j < height (2*M) eps Y j) ∧ V^J < Y^(J+1)

theorem incompatibleQ {eps Y V : ℝ} {q d q' d' : ℕ}
    (a : WinPair eps Y q d) (b : WinPair eps V q' d') (sep : 2*z eps Y ≤ z eps V) : q ≠ q' := by
  rintro rfl
  have hl := b.q_lo
  have hu := a.q_up
  unfold z at sep
  linarith

theorem incompatibleD {eps Y V : ℝ} {q d q' d' : ℕ}
    (a : WinPair eps Y q d) (b : WinPair eps V q' d') (sep : 2*h eps Y ≤ h eps V) : d ≠ d' := by
  rintro rfl
  have hl := b.d_lo
  have hu := a.d_up
  unfold h z at sep
  linarith

private theorem next_le {a : ℝ} {n : ℕ} (ha : 0 ≤ a) (hlt : a < n) : nextInt a ≤ n := by
  have hn := (Nat.floor_lt ha).2 hlt
  have hnn : ⌊a⌋₊ + 1 ≤ n := hn
  unfold nextInt
  exact_mod_cast hnn

private theorem rowTransport {M : ℕ} {eps J Y V : ℝ} {q d : ℕ}
    (he : 0 ≤ eps) (hY : 1 ≤ Y) (hV : Y ≤ V) (g : Guard M eps J Y V)
    (p : WinPair eps Y q d) : WinPair eps V q d := by
  rcases g with ⟨gz,gq,gd,-,-⟩
  have hY0 : 0 < Y := by linarith
  have hz : z eps Y ≤ z eps V := Real.rpow_le_rpow hY0.le hV (by positivity)
  have hh : h eps Y ≤ h eps V :=
    mul_le_mul hz (pow_le_pow_left₀ (Real.log_nonneg hY) (Real.log_le_log hY0 hV) 2)
      (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have qcast : 0 < (q : ℝ) := by exact_mod_cast p.q_prime.pos
  have dcast : 0 < (d : ℝ) := by exact_mod_cast p.d_prime.pos
  have pq := (Real.lt_log_iff_exp_lt qcast).1 p.q_lo
  have pd := (Real.lt_log_iff_exp_lt dcast).1 p.d_lo
  refine ⟨p.q_prime,p.q_mod,(Real.lt_log_iff_exp_lt qcast).2 (gq.trans_le (next_le (Real.exp_pos _).le pq)),
    p.q_up.trans hz,p.d_prime,p.d_mod,(Real.lt_log_iff_exp_lt dcast).2 (gd.trans_le (next_le (Real.exp_pos _).le pd)),
    p.d_up.trans hh,p.d_q,?_⟩
  intro r hr hr2 hrv
  apply p.d_small r hr hr2
  by_contra! hrY
  have := next_le (Real.rpow_nonneg hY0.le _) hrY
  exact (not_lt_of_ge (this.trans hrv)) gz

theorem goodTransport {M : ℕ} (hM : 0 < M) {eps J Y V : ℝ} {q d : ℕ}
    (he : 0 ≤ eps) (hY : 1 ≤ Y) (hV : Y ≤ V)
    (g : Guard M eps J Y V) (p : PairGood (2*M) eps Y (Y^(J+1)) q d) :
    PairGood M eps V (V^J) q d := by
  let _ : NeZero (2*M) := ⟨by omega⟩
  have div : M ∣ 2*M := dvd_mul_left M 2
  have div8 : 8*M ∣ 8*(2*M) := Nat.mul_dvd_mul_left _ div
  have divAll : 2*M*q*d ∣ 2*(2*M)*q*d := by
    exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left _ div) q) d
  refine ⟨rowTransport he hY hV g p.pair,p.coprime.coprime_dvd_left div,?_,?_⟩
  · intro ξ i j hij N _ χ hc y hy hyy
    let ξ' := DirichletCharacter.changeLevel div ξ
    have hc' : An.Induces χ (tw (fun n => ξ' (n : ZMod (2*M))) q d i j) (2*(2*M)*q*d) := by
      refine ⟨hc.1,?_⟩
      intro n hn
      have hdn : (2*M) ∣ 2*(2*M)*q*d := by exact dvd_trans (dvd_mul_left _ _) ((dvd_mul_right (2*(2*M)) q).trans (dvd_mul_right _ d))
      have hcop : n.Coprime (2*M) := hn.coprime_dvd_right hdn
      have hg : IsCoprime (n : ℤ) ((2*M : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      have hlift : ξ' (n : ZMod (2*M)) = ξ (n : ZMod M) := by
        simpa [ξ'] using DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ div hg
      simpa [tw,hlift] using hc.2 n (hn.coprime_dvd_right divAll)
    exact p.bounds ξ' i j hij N χ hc' y (hV.trans hy) (hyy.trans g.2.2.2.2.le)
  · intro ρ hρ hρN i j hij N _ χ hc s hs hb
    have hc' : An.Induces χ (tw ρ.val q d i j) (2*(2*M)*q*d) :=
      ⟨hc.1,fun n hn => hc.2 n (hn.coprime_dvd_right divAll)⟩
    exact p.boxes ρ hρ (hρN.trans div8) i j hij N χ hc' s hs (hb.trans (g.2.2.2.1 j).le)

theorem guardOpen {M : ℕ} (hM : 0 < M) {eps J Y : ℝ} (hy : 1 < Y) :
    ∃ r > (0:ℝ), ∀ V, |V-Y| < r → Guard M eps J Y V := by
  have yp : 0 < Y := by linarith
  have yne : Y ≠ 0 := yp.ne'
  have zn : ContinuousAt (z eps) Y := by unfold z; fun_prop (disch := aesop)
  have hn : ContinuousAt (h eps) Y := by unfold h; fun_prop (disch := aesop)
  have zq : ContinuousAt (fun v => Real.exp (z eps v/2)) Y := by fun_prop (disch := aesop)
  have hd : ContinuousAt (fun v => Real.exp (h eps v/2)) Y := by fun_prop (disch := aesop)
  have zsmall := zn.tendsto.eventually_lt_const (show z eps Y < nextInt (z eps Y) from Nat.lt_floor_add_one _)
  have qsmall := zq.tendsto.eventually_lt_const (show Real.exp (z eps Y/2) < nextInt (Real.exp (z eps Y / 2)) from Nat.lt_floor_add_one _)
  have dsmall := hd.tendsto.eventually_lt_const (show Real.exp (h eps Y/2) < nextInt (Real.exp (h eps Y / 2)) from Nat.lt_floor_add_one _)
  have ht (j : Fin 2) : ContinuousAt (fun v => height M eps v j) Y := by unfold height; fun_prop (disch := aesop)
  have hp (j : Fin 2) : 0 < height M eps Y j := by unfold height; positivity
  have htwo (j : Fin 2) : height (2*M) eps Y j = 2*height M eps Y j := by unfold height; push_cast; ring
  have bh (j : Fin 2) : ∀ᶠ v in 𝓝 Y, height M eps v j < height (2*M) eps Y j :=
    (ht j).tendsto.eventually_lt_const (by rw [htwo]; linarith [hp j])
  have bh' := Filter.eventually_all.2 bh
  have powlim : ContinuousAt (fun v : ℝ => v^J) Y := by fun_prop (disch := aesop)
  have pw : Y^J < Y^(J+1) := Real.rpow_lt_rpow_of_exponent_lt hy (by linarith)
  have pp := powlim.tendsto.eventually_lt_const pw
  have hall : ∀ᶠ V in 𝓝 Y, Guard M eps J Y V := by
    filter_upwards [zsmall,qsmall,dsmall,bh',pp] with V a b c f g
    exact ⟨a,b,c,f,g⟩
  obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.1 hall
  exact ⟨r,hr,fun V hv => hh (by simpa [Real.dist_eq] using hv)⟩

/-- The comparison schedule is fixed before the primes. One pair works for the
entire right-neighborhood, for two different canonical outer queries in particular. -/
theorem commonNeighborhood (p : PairEx) (M : ℕ) (hM : 0 < M) (eps J : ℝ)
    (he : 0 < eps) (h52 : eps < 1/52) (hJ : 1 ≤ J) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∃ r > (0:ℝ), ∃ q d : ℕ,
      ∀ V : ℝ, Y ≤ V → V < Y+r → PairGood M eps V (V^J) q d := by
  obtain ⟨Y₁,hp⟩ := p (2*M) (by omega) eps (J+1) he h52 (by linarith)
  refine ⟨max 2 Y₁,?_⟩
  intro Y hY
  have hY1 : 1 < Y := by have := (le_max_left (2:ℝ) Y₁).trans hY; linarith
  obtain ⟨r,hr,hg⟩ := guardOpen hM (eps := eps) (J := J) hY1
  obtain ⟨q,d,hp⟩ := hp Y ((le_max_right _ _).trans hY)
  refine ⟨r,hr,q,d,?_⟩
  intro V hV hVr
  exact goodTransport hM he.le hY1.le hV (hg V (by rw [abs_of_nonneg (sub_nonneg.mpr hV)]; linarith)) hp

/-- The original cohomological selector can be called at every resulting outer
scale with the same prime pair. No identification of the returned W or their
exceptional lists is part of this conclusion. -/
theorem successiveSelections (psi : PChar) (eps : ℝ) (he : 0 < eps) (h52 : eps < 1/52)
    (e : ℝ → ℕ) (hp : ∀ u ≥ (1:ℝ), PageN eps u (e u))
    (vwin : VWinAt psi 401) (pex : PairEx) :
    ∃ J : ℝ, 1 ≤ J ∧ ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∃ r > (0:ℝ), ∃ q d : ℕ,
      ∀ V : ℝ, Y ≤ V → V < Y+r →
        PairGood psi.N eps V (V^J) q d ∧
        ∃ W : ℝ, V ≤ W ∧ W^(2:ℝ) ≤ V^J ∧
          ∀ u : ℝ, W ≤ u → u ≤ W^(2:ℝ) → VAt psi eps 401 q d (e u) u := by
  obtain ⟨J,hJ,X₀,hW⟩ := vwin eps he h52 e hp
  have hj : 0 < J := by linarith
  obtain ⟨B,hB⟩ := commonNeighborhood pex psi.N (Nat.pos_of_ne_zero (NeZero.ne _)) eps J he h52 hJ
  refine ⟨J,hJ,max B (max X₀ 2),?_⟩
  intro Y hy
  obtain ⟨r,hr,q,d,hqd⟩ := hB Y ((le_max_left _ _).trans hy)
  refine ⟨r,hr,q,d,?_⟩
  intro V hyv hv
  have H := hqd V hyv hv
  have hvx := ((le_max_left X₀ 2).trans (le_max_right B _)).trans (hy.trans hyv)
  have hv2 := ((le_max_right X₀ 2).trans (le_max_right B _)).trans (hy.trans hyv)
  have hv1 : 1 ≤ V := by linarith
  have hu : V ≤ V^J := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hv1 hJ
  have hid : (V^J)^(1/J) = V := by
    rw [one_div,Real.rpow_rpow_inv (by linarith : 0 ≤ V) hj.ne']
  have hw := hW (V^J) (hvx.trans hu) q d
  rw [hid] at hw
  exact ⟨H,hw H.pair⟩

/-- Fix a target before choosing the primes. Every allowed query contains it
in its ambient domain; its selected arithmetic subwindow is still existential. -/
theorem prescribedAmbient (pex : PairEx) (M : ℕ) (hM : 0 < M) (eps J : ℝ)
    (he : 0 < eps) (h52 : eps < 1/52) (hJ : 1 ≤ J) :
    ∃ T : ℝ, ∀ a b Y : ℝ, T ≤ Y → Y < a → a ≤ b → b ≤ Y^J →
      ∃ r > (0:ℝ), ∃ q d : ℕ, ∀ V : ℝ, Y ≤ V → V < Y+r →
        Set.Icc a b ⊆ Set.Icc V (V^J) ∧ PairGood M eps V (V^J) q d := by
  obtain ⟨T,hT⟩ := commonNeighborhood pex M hM eps J he h52 hJ
  refine ⟨max T 1,?_⟩
  intro a b Y hy ha _ hb
  obtain ⟨r,hr,q,d,hqd⟩ := hT Y ((le_max_left _ _).trans hy)
  refine ⟨min r (a-Y),lt_min hr (by linarith),q,d,?_⟩
  intro V hyV hV
  obtain ⟨hVr,hVa⟩ : V < Y+r ∧ V < a := by
    constructor
    · linarith [min_le_left r (a-Y)]
    · linarith [min_le_right r (a-Y)]
  refine ⟨?_,hqd V hyV hVr⟩
  intro x hx
  have hy0 := (le_max_right T (1:ℝ)).trans hy
  exact ⟨hVa.le.trans hx.1,hx.2.trans (hb.trans (Real.rpow_le_rpow (by linarith) hyV (by linarith)))⟩

end SuccessivePairs

#print axioms SuccessivePairs.incompatibleQ
#print axioms SuccessivePairs.incompatibleD
#print axioms SuccessivePairs.goodTransport
#print axioms SuccessivePairs.guardOpen
#print axioms SuccessivePairs.commonNeighborhood
#print axioms SuccessivePairs.successiveSelections
#print axioms SuccessivePairs.prescribedAmbient
