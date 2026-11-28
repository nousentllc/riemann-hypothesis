import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral

noncomputable section
open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G
namespace Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit
open Classical
variable {D : D7} {L : SizeData₂ D}

def matched (d : ℕ) (b A : ℝ) : ℝ := if d = 0 then 0 else min b A
def clip (d : ℕ) (b o A : ℝ) : ℝ := if d = 0 then 0 else min o (max 0 (A-b))

theorem clip_formula (d : ℕ) (b o A : ℝ) (ho : 0 ≤ o) :
    matched d (b+o) A - matched d b A = clip d b o A := by
  unfold matched clip
  split_ifs with h
  · ring
  · simp only [min_def, max_def]
    split_ifs <;> linarith

theorem clip_bounds (d : ℕ) (b o A : ℝ) (ho : 0 ≤ o) :
    0 ≤ clip d b o A ∧ clip d b o A ≤ o := by
  by_cases hd : d = 0
  · simp [clip, hd, ho]
  · simp only [clip, if_neg hd]
    exact ⟨le_min ho (le_max_left ..), min_le_left ..⟩

theorem no_clip (d : ℕ) (b o A : ℝ) (ho : 0 ≤ o) (h : d = 0 ∨ A ≤ b) :
    clip d b o A = 0 := by
  rcases h with h | h
  · simp [clip, h]
  · simp [clip, max_eq_left (sub_nonpos.mpr h), min_eq_right ho]

theorem full_clip (d : ℕ) (b o A : ℝ) (hd : d ≠ 0) (h : b+o ≤ A) :
    clip d b o A = o := by
  simp only [clip, if_neg hd]
  apply min_eq_left
  exact le_trans (by linarith : o ≤ A-b) (le_max_right ..)

theorem favorable_lift (d : ℕ) (b o A k : ℝ) :
    o-k-clip d b o A ≤ 0 ↔ o-clip d b o A ≤ k := by constructor <;> intro h <;> linarith

abbrev Pos (D : D7) (p : ℕ) := Fin (addOrderOf (hP D p))
def oddT (D : D7) (p : ℕ) (t0 : HH D) := (topsPos D p t0).filter (fun y => ¬ IsTypeV y)
def dist (D : D7) (p : ℕ) (t0 : HH D) (y : Pos D p) := dMinus (topsPos D p t0) y
def predCap (D : D7) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) (y : Pos D p) : ℝ :=
  (a (phi D p t0 (posAdd y (addOrderOf (hP D p)-dist D p t0 y))) : ℝ) / (p : ℝ) ^ dist D p t0 y
def used (D : D7) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) (W : Pos D p → ℝ) : ℝ :=
  ∑ y ∈ oddT D p t0, matched (dist D p t0 y) (W y) (predCap D p t0 a y)
def oddGain (X : Inst D L) (p : ℕ) (t0 : HH D) (b : HH D → ℤ) (j : ℕ) : ℝ :=
  ∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false,s) - (b s : ℝ))
def allPartners (X : Inst D L) (p : ℕ) (t0 : HH D) (a b : HH D → ℤ) (j : ℕ) : ℝ :=
  ∑ s ∈ (topsOn X p t0).filter (fun s => IsV X p s), Mn X a b p j s
def unused (X : Inst D L) (p : ℕ) (t0 : HH D) (a b : HH D → ℤ) (j : ℕ) : ℝ :=
  allPartners X p t0 a b j - used D p t0 a (fun y => fill X b j (false, phi D p t0 y))
def row (X : Inst D L) (p : ℕ) (t0 : HH D) (a b : HH D → ℤ) (j : ℕ) (y : Pos D p) : ℝ :=
  let o := X.off j (false, phi D p t0 y)
  o - kaJ D j - clip (dist D p t0 y) (b (phi D p t0 y)) o (predCap D p t0 a y)

theorem unused_nonneg (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p)))
    {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ) : 0 ≤ unused X p t0 a b j := by
  have hmemT : ∀ y ∈ topsPos D p t0, phi D p t0 y ∈ D.host.TT := fun _ hy => (Finset.mem_filter.1 hy).2
  have hk := kink h1 (topsPos D p t0) (p : ℝ) (by exact_mod_cast hp.two_le)
    (fun i => (a (phi D p t0 i) : ℝ)) (fun i => fill X b j (false, phi D p t0 i))
    (fun x hx => by have := (a_bounds P hW (hmemT x hx)).2.2; linarith [sc_one_lt_a L.sc])
    (fun x => by have := fill_ge_one X P hW j (false, phi D p t0 x); linarith)
  unfold unused allPartners
  apply sub_nonneg.mpr
  rw [sum_topsOn_V X hc h0]
  refine hk.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro x _
  unfold Mn
  apply tsum_congr
  intro e
  rw [partner_of_central hc, phi_posAdd]

theorem exact_excess (X : Inst D L) (P : ParameterChoice' D L) (a b : HH D → ℤ)
    {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ) :
    oddGain X p t0 b j + used D p t0 a (fun y => (b (phi D p t0 y) : ℝ)) - allPartners X p t0 a b j =
    (∑ y ∈ oddT D p t0, row X p t0 a b j y) - unused X p t0 a b j := by
  obtain ⟨h500, _, hwb, _, _⟩ := base P
  have hbx : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) (sc_x_pos L.sc).le
  have hsum := Finset.sum_congr (s₁ := oddT D p t0) rfl (g := row X p t0 a b j) (f := fun y =>
    (fillG X b j (false, phi D p t0 y) - (b (phi D p t0 y) : ℝ)) +
      matched (dist D p t0 y) (b (phi D p t0 y)) (predCap D p t0 a y) -
      matched (dist D p t0 y) (fill X b j (false, phi D p t0 y)) (predCap D p t0 a y)) (by
    intro y hy
    have ht : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
    have hf : fill X b j (false,phi D p t0 y) = (b (phi D p t0 y) : ℝ) + X.off j (false,phi D p t0 y) := by
      unfold fill
      rw [if_pos ⟨rfl,ht⟩]
    have ho := hbx.trans (X.off_top j (false,phi D p t0 y) ⟨rfl,ht⟩).1
    have he := clip_formula (dist D p t0 y) (b (phi D p t0 y)) _ (predCap D p t0 a y) ho
    unfold fillG row
    rw [hf]
    linarith only [he])
  unfold oddGain unused used
  rw [sum_topsOn_nV X hc h0]
  change (∑ y ∈ oddT D p t0, (fillG X b j (false, phi D p t0 y) - (b (phi D p t0 y) : ℝ))) + _ - _ = _
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum ⊢
  linarith only [hsum]

theorem signed_orbit_bound (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p)))
    {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ) :
    oddGain X p t0 b j + used D p t0 a (fun y => (b (phi D p t0 y) : ℝ)) - allPartners X p t0 a b j ≤
      ((oddT D p t0).card : ℝ) * (L.sc.b'/L.sc.x + L.etaSz - kaJ D j) := by
  rw [exact_excess X P a b hc h0 j]
  have hu := unused_nonneg X P hW hp hc h1 h0 j
  obtain ⟨h500, _, hwb, _, _⟩ := base P
  have hbx : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) (sc_x_pos L.sc).le
  have hrow : ∀ y ∈ oddT D p t0, row X p t0 a b j y ≤ L.sc.b'/L.sc.x + L.etaSz - kaJ D j := by
    intro y hy
    have ht : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
    obtain ⟨hol,hou⟩ := X.off_top j (false,phi D p t0 y) ⟨rfl,ht⟩
    have hcl := (clip_bounds (dist D p t0 y) (b (phi D p t0 y)) _ (predCap D p t0 a y) (hbx.trans hol)).1
    unfold row
    linarith only [hcl,hou]
  calc
    _ ≤ ∑ y ∈ oddT D p t0, row X p t0 a b j y := sub_le_self _ hu
    _ ≤ ∑ _y ∈ oddT D p t0, (L.sc.b'/L.sc.x + L.etaSz - kaJ D j) := Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


/-- A row at distance at least three cannot clip above the cubic prime threshold. -/
theorem deep_row (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (t0 : HH D) (j : ℕ) {y : Pos D p} (hy : y ∈ oddT D p t0)
    (hd : 3 ≤ dist D p t0 y) (hp3 : 2 * L.sc.X' ≤ (p : ℝ)^3) :
    row X p t0 a b j y = X.off j (false,phi D p t0 y) - kaJ D j := by
  have ht : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
  have hd0 : dist D p t0 y ≠ 0 := by omega
  have hm := (dMinus_spec (topsPos D p t0) y hd0).2.2.1
  have hprev := (a_bounds P hW (Finset.mem_filter.1 hm).2).2.1
  have hbot := (hW _ ht).2.2
  have hdiv : 0 < L.sc.X' := Real.exp_pos _
  have hab : L.sc.a = L.sc.b' * L.sc.X' := by unfold Scale.b'; field_simp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpD := pow_le_pow_right₀ hp1 hd
  have hmul := mul_le_mul_of_nonneg_left (hp3.trans hpD) (sc_b'_nonneg L.sc)
  have hcap : predCap D p t0 a y ≤ (b (phi D p t0 y) : ℝ) := by
    apply le_trans _ hbot
    unfold predCap
    apply (div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < p) _)).2
    change (a (phi D p t0 (posAdd y (addOrderOf (hP D p) - dist D p t0 y))) : ℝ) ≤ 2 * L.sc.a at hprev
    nlinarith only [hprev,hab,hmul]
  have ho := (div_nonneg (sc_b'_nonneg L.sc) (sc_x_pos L.sc).le).trans (X.off_top j (false,phi D p t0 y) ⟨rfl,ht⟩).1
  simp only [row]
  rw [no_clip _ _ _ _ ho (Or.inr hcap), sub_zero]

/-- The full box places an upper endpoint on the retained level b. -/
theorem boxed_first_row (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    (K : Consts) {p : ℕ} (hp : p.Prime) (t0 : HH D) (j : ℕ) {y : Pos D p} (hy : y ∈ oddT D p t0)
    (hd : dist D p t0 y = 1) (hbox : b (phi D p t0 y) ∈ winB D K L.sc)
    (hmargin : (L.sc.b' + Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k +
      (L.sc.b' / L.sc.x + L.etaSz)) * (p : ℝ) ≤ L.sc.a) :
    row X p t0 a b j y = -kaJ D j := by
  have ht : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
  have hd0 : dist D p t0 y ≠ 0 := by omega
  have hm := (dMinus_spec (topsPos D p t0) y hd0).2.2.1
  have hprev := (a_bounds P hW (Finset.mem_filter.1 hm).2).2.2
  have hb : (b (phi D p t0 y) : ℝ) ≤ _ := (Int.le_floor.mp (Finset.mem_Icc.mp hbox).2)
  have ho := (X.off_top j (false,phi D p t0 y) ⟨rfl,ht⟩).2
  have hsum := add_le_add hb ho
  have hcap : (b (phi D p t0 y) : ℝ) + X.off j (false,phi D p t0 y) ≤ predCap D p t0 a y := by
    unfold predCap
    rw [show (p : ℝ) ^ dist D p t0 y = p by rw [hd,pow_one]]
    apply (le_div_iff₀ (by exact_mod_cast hp.pos : (0 : ℝ) < p)).2
    exact (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg p)).trans (hmargin.trans hprev)
  simp only [row]
  rw [full_clip _ _ _ _ hd0 hcap]
  ring


/-- The finite set of odd exponents charged to the retained even source x. -/
def charged {n : ℕ} (TT : Finset (Fin n)) (x : Fin n) : Finset ℕ :=
  (((TT.filter (fun y => ¬ IsTypeV y)).filter (fun y => dMinus TT y ≠ 0)).filter
    (fun y => posAdd y (n - dMinus TT y) = x)).image (dMinus TT)

def skipped {n : ℕ} (TT : Finset (Fin n)) (q : ℝ) (a W : Fin n → ℝ) : ℝ :=
  ∑ x ∈ TT.filter IsTypeV, ∑' e : ↑((charged TT x : Set ℕ)ᶜ),
    if Odd (e : ℕ) then min (a x / q ^ (e : ℕ)) (W (posAdd x e)) else 0

/-- Preserve the unused summands at the last inequality in the pinned proof of `kink`. -/
theorem series_partition {n' : ℕ} (hn : Even n') (TT : Finset (Fin n')) (q : ℝ) (hq : 2 ≤ q) (a W : Fin n' → ℝ)
    (ha : ∀ x ∈ TT, 0 ≤ a x) (hW : ∀ x, 0 ≤ W x) :
    (∑ x ∈ TT.filter IsTypeV, ∑' e : ℕ, (if Odd e then min (a x / q ^ e) (W (posAdd x e)) else 0)) =
    (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else min (W y) (a (posAdd y (n' - dMinus TT y)) / q ^ dMinus TT y))) +
      skipped TT q a W := by
  set S := (TT.filter (fun y => ¬ IsTypeV y)).filter (fun y => dMinus TT y ≠ 0) with hS
  set xm : Fin n' → Fin n' := fun y => posAdd y (n' - dMinus TT y) with hxm
  set g : Fin n' → ℕ → ℝ := fun x e => min (a x / q ^ e) (W (posAdd x e)) with hg
  have h1 : ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else min (W y) (a (xm y) / q ^ dMinus TT y)) =
      ∑ y ∈ S, g (xm y) (dMinus TT y) := by
    symm
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hd : dMinus TT y = 0
    · rw [if_pos hd, if_neg (not_not.2 hd)]
    · rw [if_neg hd, if_pos hd]
      simp only [hg, hxm]
      rw [posAdd_back y _ (dMinus_spec TT y hd).2.1, min_comm]
  rw [h1]
  have hmaps : ∀ y ∈ S, xm y ∈ TT.filter (fun x => IsTypeV x) := by
    intro y hy
    have hd := (Finset.mem_filter.1 hy).2
    obtain ⟨_, _, h3, h4⟩ := dMinus_spec TT y hd
    exact Finset.mem_filter.2 ⟨h3, h4⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold skipped
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hxT := (Finset.mem_filter.1 hx).1
  set Fb := S.filter (fun y => xm y = x) with hFb
  have hinj : ∀ y ∈ Fb, ∀ y' ∈ Fb, dMinus TT y = dMinus TT y' → y = y' := by
    intro y hy y' hy' hdd
    have e1 : xm y = x := (Finset.mem_filter.1 hy).2
    have e2 : xm y' = x := (Finset.mem_filter.1 hy').2
    have d1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
    have d2 := (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).2
    have b1 : posAdd (xm y) (dMinus TT y) = y := posAdd_back y _ (dMinus_spec TT y d1).2.1
    have b2 : posAdd (xm y') (dMinus TT y') = y' := posAdd_back y' _ (dMinus_spec TT y' d2).2.1
    calc y = posAdd (xm y) (dMinus TT y) := b1.symm
      _ = posAdd (xm y') (dMinus TT y') := by rw [e1, e2, hdd]
      _ = y' := b2
  have h2 : ∑ y ∈ Fb, g (xm y) (dMinus TT y) =
      ∑ e ∈ Fb.image (dMinus TT), (if Odd e then g x e else 0) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro y hy
    have e1 : xm y = x := (Finset.mem_filter.1 hy).2
    have hyS := (Finset.mem_filter.1 hy).1
    have d1 := (Finset.mem_filter.1 hyS).2
    have o1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hyS).1).2
    rw [if_pos (dMinus_odd hn TT y o1 d1), e1]
  rw [h2]
  have hg0 : ∀ e, 0 ≤ g x e := fun e => le_min (div_nonneg (ha x hxT) (by positivity)) (hW _)
  have hs := summable_if_of_le q (a x) hq (g x) Odd hg0 (fun e => min_le_left _ _)
  exact (hs.sum_add_tsum_compl (s := Fb.image (dMinus TT))).symm

/-- Positive unused slack is the series over precisely the complementary exponent indices. -/
theorem unused_eq_skipped (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p)))
    {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ) :
    unused X p t0 a b j = skipped (topsPos D p t0) (p : ℝ) (fun i => (a (phi D p t0 i) : ℝ))
      (fun i => fill X b j (false, phi D p t0 i)) := by
  have hmemT : ∀ y ∈ topsPos D p t0, phi D p t0 y ∈ D.host.TT := fun _ hy => (Finset.mem_filter.1 hy).2
  have hs := series_partition h1 (topsPos D p t0) (p : ℝ) (by exact_mod_cast hp.two_le)
    (fun i => (a (phi D p t0 i) : ℝ)) (fun i => fill X b j (false, phi D p t0 i))
    (fun x hx => by have := (a_bounds P hW (hmemT x hx)).2.2; linarith [sc_one_lt_a L.sc])
    (fun x => by have := fill_ge_one X P hW j (false, phi D p t0 x); linarith)
  have hR : ∑ x ∈ (topsPos D p t0).filter IsTypeV, ∑' e : ℕ, (if Odd e then
      min ((a (phi D p t0 x) : ℝ) / (p : ℝ) ^ e) (fill X b j (false, phi D p t0 (posAdd x e))) else 0) =
      allPartners X p t0 a b j := by
    unfold allPartners
    rw [sum_topsOn_V X hc h0]
    apply Finset.sum_congr rfl
    intro x _
    unfold Mn
    apply tsum_congr
    intro e
    rw [partner_of_central hc, phi_posAdd]
  unfold unused
  rw [hR] at hs
  exact sub_eq_of_eq_add' hs

/-- The positive part preserves the bulk squeeze when the reference count is nonnegative. -/
theorem positive_part_squeeze (T M low high : ℝ) (hm : 0 ≤ M) (hl : M-low ≤ T) (hu : T ≤ M+high)
    (hh : 0 ≤ high) : M-low ≤ max 0 T ∧ max 0 T ≤ M+high :=
  ⟨hl.trans (le_max_right ..), max_le (by linarith) hu⟩


/-- A retained even source spends its first odd column exactly when its successor is retained. -/
theorem one_charged_iff {n : ℕ} (hn : Even n) (TT : Finset (Fin n)) {x : Fin n}
    (hx : x ∈ TT) (he : IsTypeV x) : 1 ∈ charged TT x ↔ posAdd x 1 ∈ TT := by
  have hn1 : 1 ≤ n := by have := x.isLt; omega
  have hback : posAdd (posAdd x 1) (n-1) = x := by
    apply Fin.ext
    unfold posAdd
    simp only
    rw [Nat.mod_add_mod, show x.val + 1 + (n-1) = x.val + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt x.2]
  have hodd : ¬ IsTypeV (posAdd x 1) := by
    unfold IsTypeV at he ⊢
    unfold posAdd
    simp only
    obtain ⟨q,hq⟩ := hn
    have hn2 : 2 ∣ n := ⟨q,by omega⟩
    rw [Nat.even_iff, Nat.mod_mod_of_dvd _ hn2]
    rw [Nat.even_iff] at he
    omega
  unfold charged
  constructor
  · intro h
    obtain ⟨y,hy,hd⟩ := Finset.mem_image.mp h
    obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hy
    obtain ⟨h3,h4⟩ := Finset.mem_filter.mp h1
    have heq := posAdd_back y _ (dMinus_spec TT y h4).2.1
    rw [h2,hd] at heq
    exact heq ▸ (Finset.mem_filter.mp h3).1
  · intro ht
    let y := posAdd x 1
    have hP : (fun d : ℕ => 0 < d ∧ d ≤ n ∧ posAdd y (n-d) ∈ TT ∧ IsTypeV (posAdd y (n-d))) 1 := by
      exact ⟨by decide, hn1, hback ▸ hx, hback ▸ he⟩
    have hd : dMinus TT y = 1 := by
      unfold dMinus
      rw [dif_pos ⟨1,hP⟩]
      have hle := Nat.find_min' (p := fun d : ℕ => 0 < d ∧ d ≤ n ∧ posAdd y (n-d) ∈ TT ∧ IsTypeV (posAdd y (n-d))) (H := ⟨1,hP⟩) hP
      have hpos := (Nat.find_spec (p := fun d : ℕ => 0 < d ∧ d ≤ n ∧ posAdd y (n-d) ∈ TT ∧ IsTypeV (posAdd y (n-d))) ⟨1,hP⟩).1
      omega
    exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨ht,hodd⟩,by omega⟩,by rw [hd]; exact hback⟩,hd⟩

/-- A missing retained successor is a thin place even when its integer level was unconstrained. -/
theorem first_thin (X : Inst D L) (b : HH D → ℤ) (p : ℕ) (t0 : HH D) (j : ℕ)
    {x : Pos D p} (hx : posAdd x 1 ∉ topsPos D p t0) :
    fill X b j (false, phi D p t0 (posAdd x 1)) ≤ L.sc.w'' D.R.n + L.etaSz := by
  have ht : phi D p t0 (posAdd x 1) ∉ D.host.TT := fun h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hthin : IsThinPl D (false, phi D p t0 (posAdd x 1)) := ⟨fun h => ht h.2,fun h => Bool.false_ne_true h.1⟩
  simpa [fill,ht] using (X.off_thin j _ hthin).2


/-- A column's uncharged exponent-one cost plus the entire geometric odd tail. -/
theorem skipped_column_bound (q a : ℝ) (hq : 2 ≤ q) (ha : 0 ≤ a) (w : ℕ → ℝ)
    (hw : ∀ e, 0 ≤ w e) (S : Finset ℕ) :
    (∑' e : ↑((S : Set ℕ)ᶜ), if Odd (e : ℕ) then min (a / q ^ (e : ℕ)) (w e) else 0) ≤
    (if 1 ∈ S then 0 else w 1) + a / (q * (q^2-1)) := by
  let f (e : ℕ) := if Odd e then min (a/q^e) (w e) else 0
  let g (e : ℕ) := if Odd e then a/q^e else 0
  let spike (e : ℕ) := if e = 1 then g 1 - f 1 else 0
  have hq0 : 0 < q := by linarith
  have hf0 : ∀ e, 0 ≤ f e := fun e => by
    dsimp [f]
    split_ifs
    · exact le_min (div_nonneg ha (pow_nonneg hq0.le _)) (hw _)
    · exact le_rfl
  have hf := summable_if_of_le q a hq (fun e => min (a/q^e) (w e)) Odd
    (fun e => le_min (div_nonneg ha (pow_nonneg hq0.le _)) (hw _)) (fun _ => min_le_left ..)
  have hg := summable_if_of_le q a hq (fun e => a/q^e) Odd (fun _ => div_nonneg ha (pow_nonneg hq0.le _)) (fun _ => le_rfl)
  have hs : HasSum spike (g 1-f 1) := hasSum_ite_eq 1 _
  have hc : ∀ e, f e + spike e ≤ g e := by
    intro e
    by_cases he : e=1
    · subst e; simp [spike]
    · simp only [spike, if_neg he, add_zero, f, g]
      split_ifs
      · exact min_le_left ..
      · exact le_rfl
  have hsum := Summable.tsum_le_tsum hc (hf.add hs.summable) hg
  rw [hf.tsum_add hs.summable, hs.tsum_eq] at hsum
  have hgval : (∑' e, g e) = q/(q^2-1)*a := tsum_odd q a hq Odd (fun _ => Iff.rfl)
  have h1val : g 1 = a/q := by simp [g]
  have ht : q/(q^2-1)*a - a/q = a/(q*(q^2-1)) := by
    have hqq : 0 < q^2-1 := by nlinarith
    field_simp
    ring
  have hhead : f 1 ≤ w 1 := by simp [f]
  have hpart : (∑ e ∈ S, f e) + (∑' e : ↑((S : Set ℕ)ᶜ), f e) = ∑' e, f e := hf.sum_add_tsum_compl
  change (∑' e : ↑((S : Set ℕ)ᶜ), f e) ≤ _
  by_cases h1 : 1 ∈ S
  · rw [if_pos h1,zero_add]
    have hused : f 1 ≤ ∑ e ∈ S, f e := Finset.single_le_sum (fun e _ => hf0 e) h1
    linarith only [hused,hpart,ht,hsum,h1val,hgval]
  · rw [if_neg h1]
    have hused : 0 ≤ ∑ e ∈ S, f e := Finset.sum_nonneg (fun e _ => hf0 e)
    linarith only [hused,hpart,ht,hsum,h1val,hgval,hhead]

/-- The entire uncharged series is bounded by the number of holes and the odd tail. -/
theorem unused_le_holes_tail (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p)))
    {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ) :
    unused X p t0 a b j ≤ ∑ x ∈ (topsPos D p t0).filter IsTypeV,
      ((if posAdd x 1 ∈ topsPos D p t0 then 0 else L.sc.w'' D.R.n + L.etaSz) +
        2 * L.sc.a / ((p : ℝ) * ((p : ℝ)^2-1))) := by
  rw [unused_eq_skipped X P hW hp hc h1 h0 j]
  unfold skipped
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hxT,hxE⟩ := Finset.mem_filter.mp hx
  obtain ⟨_,hcap,hlower⟩ := a_bounds P hW (Finset.mem_filter.mp hxT).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnn : 0 ≤ (a (phi D p t0 x) : ℝ) := (by linarith [sc_one_lt_a L.sc] : 0 ≤ L.sc.a).trans hlower
  have hcap' : (a (phi D p t0 x) : ℝ) ≤ 2 * L.sc.a := hcap
  refine (skipped_column_bound (p : ℝ) (a (phi D p t0 x)) hp2 hnn
    (fun e => fill X b j (false,phi D p t0 (posAdd x e))) (fun e => by
      linarith [fill_ge_one X P hW j (false,phi D p t0 (posAdd x e))]) _).trans ?_
  apply add_le_add
  · have hlink := one_charged_iff h1 _ hxT hxE
    by_cases hh : posAdd x 1 ∈ topsPos D p t0
    · rw [if_pos (hlink.mpr hh), if_pos hh]
    · rw [if_neg (hlink.not.mpr hh), if_neg hh]
      exact first_thin X b p t0 j hh
  · apply div_le_div_of_nonneg_right hcap'
    apply mul_nonneg (Nat.cast_nonneg _)
    nlinarith


/-- At a boxed bulk prime, only odd tops without an adjacent even predecessor pay the offset. -/
theorem bulk_row (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    (K : Consts) {p : ℕ} (hp : p.Prime) (h1 : Even (addOrderOf (hP D p))) (t0 : HH D) (j : ℕ)
    {y : Pos D p} (hy : y ∈ oddT D p t0) (hbox : b (phi D p t0 y) ∈ winB D K L.sc)
    (hp3 : 2 * L.sc.X' ≤ (p : ℝ)^3)
    (hmargin : (L.sc.b' + Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k +
      (L.sc.b' / L.sc.x + L.etaSz)) * (p : ℝ) ≤ L.sc.a) :
    row X p t0 a b j y = (if dist D p t0 y = 1 then 0 else X.off j (false,phi D p t0 y)) - kaJ D j := by
  split_ifs with hd
  · simpa using boxed_first_row X P hW K hp t0 j hy hd hbox hmargin
  · by_cases hd0 : dist D p t0 y = 0
    · simp [row,clip,hd0]
    · have ho := dMinus_odd h1 (topsPos D p t0) y (Finset.mem_filter.mp hy).2 hd0
      obtain ⟨k,hk⟩ := ho
      change dist D p t0 y = 2*k+1 at hk
      exact deep_row X P hW hp t0 j hy (by omega) hp3

/-- Source-level signed bulk interval. The lower bound retains the actual number of thin first columns. -/
theorem bulk_sandwich (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    (K : Consts) {p : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p) (h1 : Even (addOrderOf (hP D p)))
    {t0 : HH D} (h0 : X.bs (stepP D p) t0 = t0) (j : ℕ)
    (hbox : ∀ y ∈ oddT D p t0, b (phi D p t0 y) ∈ winB D K L.sc)
    (hp3 : 2 * L.sc.X' ≤ (p : ℝ)^3)
    (hmargin : (L.sc.b' + Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k +
      (L.sc.b' / L.sc.x + L.etaSz)) * (p : ℝ) ≤ L.sc.a) :
    let total := oddGain X p t0 b j + used D p t0 a (fun y => (b (phi D p t0 y) : ℝ)) - allPartners X p t0 a b j
    let orbitRows (level : ℝ) := ∑ y ∈ oddT D p t0, ((if dist D p t0 y = 1 then 0 else level) - kaJ D j)
    let tail := ∑ x ∈ (topsPos D p t0).filter IsTypeV,
      ((if posAdd x 1 ∈ topsPos D p t0 then 0 else L.sc.w'' D.R.n + L.etaSz) +
        2 * L.sc.a / ((p : ℝ) * ((p : ℝ)^2-1)))
    orbitRows (L.sc.b'/L.sc.x) - tail ≤ total ∧ total ≤ orbitRows (L.sc.b'/L.sc.x + L.etaSz) := by
  dsimp only
  rw [exact_excess X P a b hc h0 j]
  have bounds : ∀ y ∈ oddT D p t0,
      (if dist D p t0 y = 1 then 0 else L.sc.b'/L.sc.x) - kaJ D j ≤ row X p t0 a b j y ∧
      row X p t0 a b j y ≤ (if dist D p t0 y = 1 then 0 else L.sc.b'/L.sc.x+L.etaSz) - kaJ D j := by
    intro y hy
    have ht : phi D p t0 y ∈ D.host.TT := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    obtain ⟨lo,hi⟩ := X.off_top j (false,phi D p t0 y) ⟨rfl,ht⟩
    rw [bulk_row X P hW K hp h1 t0 j hy (hbox y hy) hp3 hmargin]
    by_cases hd : dist D p t0 y = 1 <;> simp [hd,lo,hi]
  have hl := Finset.sum_le_sum (fun y hy => (bounds y hy).1)
  have hu := Finset.sum_le_sum (fun y hy => (bounds y hy).2)
  exact ⟨sub_le_sub hl (unused_le_holes_tail X P hW hp hc h1 h0 j),
    le_trans (sub_le_self _ (unused_nonneg X P hW hp hc h1 h0 j)) hu⟩

end Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit

#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.clip_formula
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.clip_bounds
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.no_clip
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.full_clip
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.favorable_lift
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.unused_nonneg
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.exact_excess
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.signed_orbit_bound
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.deep_row
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.boxed_first_row
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.series_partition
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.unused_eq_skipped
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.positive_part_squeeze
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.one_charged_iff
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.first_thin
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.skipped_column_bound
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.unused_le_holes_tail
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.bulk_row
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit.bulk_sandwich
