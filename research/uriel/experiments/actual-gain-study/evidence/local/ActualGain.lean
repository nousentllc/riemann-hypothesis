import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral

noncomputable section
open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G
namespace Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit
open Classical
variable {D : D7} {L : SizeData₂ D}

def posDemand (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  max 0 (al L a s / (p : ℝ)^e - capU X b p j s e)
def minCredit (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  min (al L a s / (p : ℝ)^e) (capU X b p j s e)
def excluded (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e, if Excl D p s e then posDemand X a b p j s e else 0
def kept (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e, if Odd e ∧ ¬ Excl D p s e then posDemand X a b p j s e else 0
def minima (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e, if Odd e then minCredit X a b p j s e else 0
def credit (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  (∑ s ∈ topsOn X p t0, excluded X a b p j s) +
  (∑ s ∈ (topsOn X p t0).filter (IsV X p), minima X a b p j s)

theorem source_nonneg (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    (p : ℕ) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    0 ≤ al L a s ∧ ∀ e, 0 ≤ capU X b p j s e := by
  have ha := (a_bounds P hW hs).1
  obtain ⟨_,_,_,_,hSc⟩ := base P
  have hk := kaJ_le P j hj
  refine ⟨sub_nonneg.mpr ha,?_⟩
  intro e
  have hf := fill_ge_one X P hW j (partner D p s e)
  unfold capU fillG
  linarith

theorem demand_split (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    kept X a b p j s + excluded X a b p j s = ∑' e, if Odd e then posDemand X a b p j s e else 0 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨ha,hcap⟩ := source_nonneg X P hW p hj hs
  have hn (e : ℕ) : 0 ≤ posDemand X a b p j s e := le_max_left ..
  have hle (e : ℕ) : posDemand X a b p j s e ≤ al L a s / (p : ℝ)^e :=
    max_le (div_nonneg ha (by positivity)) (sub_le_self _ (hcap e))
  have hsum (Q : ℕ → Prop) [DecidablePred Q] := summable_if_of_le (p : ℝ) (al L a s) hp2
    (posDemand X a b p j s) Q hn hle
  unfold kept excluded
  rw [← (hsum (fun e => Odd e ∧ ¬ Excl D p s e)).tsum_add (hsum (Excl D p s))]
  have heq : (∑' e, ((if Odd e ∧ ¬ Excl D p s e then posDemand X a b p j s e else 0) +
      (if Excl D p s e then posDemand X a b p j s e else 0))) =
      ∑' e, (if Odd e then posDemand X a b p j s e else 0) := by
    apply tsum_congr
    intro e
    by_cases he : Excl D p s e
    · simp [he,he.1]
    · simp [he]
  exact heq

theorem column_partition (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    kept X a b p j s + excluded X a b p j s + minima X a b p j s = gam p * al L a s := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨ha,hcap⟩ := source_nonneg X P hW p hj hs
  rw [demand_split X P hW hp hj hs]
  exact tsum_pos_add_min (p : ℝ) (al L a s) hp2 ha (fun e => capU X b p j s e) hcap Odd (fun _ => Iff.rfl)

/-- Common dl cancels for *every* raw branch comparison, even before a high-prime expansion. -/
theorem raw_difference (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    gU X K a b p j t0 - Pr X K b p j t0 - g0 X K a b p j t0 = credit X a b p j t0 - Pr X K b p j t0 := by
  have hsum := Finset.sum_congr (s₁ := topsOn X p t0) rfl (fun s hs =>
    column_partition X P hW hp hj (Finset.mem_filter.mp hs).1)
  have hsplit := Finset.sum_filter_add_sum_filter_not (topsOn X p t0) (IsV X p) (minima X a b p j)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  change gam p * (∑ s ∈ topsOn X p t0, al L a s) - (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), minima X a b p j s) -
    dl X K p t0 - Pr X K b p j t0 - ((∑ s ∈ topsOn X p t0, kept X a b p j s) - dl X K p t0) = _
  unfold credit
  linarith only [hsum,hsplit]

/-- At high primes, `Pr` charges signed top offsets on odd retained rows plus this fixed orbit cost. -/
theorem high_charge (X : Inst D L) (K : Consts) (b : HH D → ℤ) {p : ℕ} (hp0 : L.sc.p0 D.R.k ≤ (p : ℝ)) (j : ℕ) (t0 : HH D) :
    Pr X K b p j t0 = (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (X.off j (false,s) - kaJ D j)) +
      K.Pr1 * (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by
  unfold Pr
  rw [if_pos hp0]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hh : s ∈ D.host.TT := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  simp [fillG,fill,hh]
  ring

def improvement (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  max 0 (credit X a b p j t0 - Pr X K b p j t0 - max 0 (-g0 X K a b p j t0))

theorem served_max (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    max (gU X K a b p j t0-Pr X K b p j t0) (max (g0 X K a b p j t0) 0) =
      max (g0 X K a b p j t0) 0 + improvement X K a b p j t0 := by
  have h := raw_difference X K P hW hp hj t0
  unfold improvement
  simp only [max_def]
  split_ifs <;> linarith

/-- Once the stop guard is false, all reps contribute baseline, and only served reps add improvement. -/
theorem gainP_split (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D)
    (hgo : ¬ ((IsResidueClassZero D p ∧ hP D p = 0) ∨ L.sc.X'' D.R.n < (p : ℝ))) :
    gainP X K a b p j = (∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0) +
      ∑ t0 ∈ VV X K a b p, improvement X K a b p j t0 := by
  have hsub : VV X K a b p ⊆ reps X p := by
    unfold VV goodReps
    split_ifs
    · exact Finset.filter_subset ..
    · exact Finset.empty_subset _
  have hrec := Finset.sum_sdiff (f := fun t0 => max (g0 X K a b p j t0) 0) hsub
  unfold gainP
  rw [if_neg hgo]
  simp only [served_max X K P hW hp hj,Finset.sum_add_distrib]
  linarith only [hrec]

/-- First positive distance has no earlier competitors. A nonzero central step makes the successor distinct. -/
theorem excl_one_iff {p : ℕ} (hc : IsResidueClassZero D p) (hn : hP D p ≠ 0) (s : HH D) :
    Excl D p s 1 ↔ s + hP D p ∈ D.host.TT := by
  have hpart : partner D p s 1 = (false,s+hP D p) := by rw [partner_of_central hc,one_nsmul]
  constructor
  · rintro ⟨_,t,ht,_,_,h,_⟩
    rw [hpart] at h
    obtain rfl : s+hP D p = t := congrArg Prod.snd h
    exact ht
  · intro ht
    refine ⟨by decide,_,ht,?_,by decide,hpart,?_⟩
    · simpa using hn
    · intro e hpos hlt
      omega

/-- All odd, excluded demands at distance beyond one vanish above the cubic threshold. -/
theorem excluded_deep_zero (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hp3 : 2 * L.sc.X' ≤ (p : ℝ)^3) {j : ℕ} (hj : j ∈ SizeData₂.lifts D)
    {s : HH D} (hs : s ∈ D.host.TT) {e : ℕ} (he : Excl D p s e) (h1 : e ≠ 1) : posDemand X a b p j s e = 0 := by
  obtain ⟨ho,t,ht,_,_,hpart,_⟩ := he
  obtain ⟨k,hk⟩ := ho
  have he3 : 3 ≤ e := by omega
  obtain ⟨_,_,_,hcg,hSc⟩ := base P
  have hk := kaJ_le P j hj
  have hb := (hW t ht).2.2
  have hoff := (X.off_top j (false,t) ⟨rfl,ht⟩).1
  have hoff_nn := div_nonneg (sc_b'_nonneg L.sc) (sc_x_pos L.sc).le
  have hcap : L.sc.b' ≤ capU X b p j s e := by
    unfold capU fillG
    rw [hpart]
    simp [fill,ht]
    linarith
  have ha := (a_bounds P hW hs).2.1
  have hdiv : 0 < L.sc.X' := Real.exp_pos _
  have hscale : L.sc.a = L.sc.b' * L.sc.X' := by unfold Scale.b'; field_simp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hmult := mul_le_mul_of_nonneg_left (hp3.trans (pow_le_pow_right₀ hp1 he3)) (sc_b'_nonneg L.sc)
  apply max_eq_left
  apply sub_nonpos.mpr
  refine le_trans ?_ hcap
  apply (div_le_iff₀ (pow_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p) _)).2
  unfold al
  nlinarith only [hscale,hmult,ha,hcg]

theorem excluded_eq_first (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hp3 : 2 * L.sc.X' ≤ (p : ℝ)^3) {j : ℕ} (hj : j ∈ SizeData₂.lifts D)
    {s : HH D} (hs : s ∈ D.host.TT) : excluded X a b p j s = (if Excl D p s 1 then posDemand X a b p j s 1 else 0) := by
  unfold excluded
  rw [tsum_eq_single 1]
  intro e he
  by_cases hex : Excl D p s e
  · rw [if_pos hex,excluded_deep_zero X P hW hp hp3 hj hs hex he]
  · rw [if_neg hex]

/-- First-exponent credit before payment of the source price. -/
def first (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  (if Excl D p s 1 then posDemand X a b p j s 1 else 0) + (if IsV X p s then minCredit X a b p j s 1 else 0)

theorem first_directed (X : Inst D L) (a b : HH D → ℤ) {p : ℕ} (hc : IsResidueClassZero D p) (hn : hP D p ≠ 0)
    (j : ℕ) (s : HH D) : first X a b p j s =
      if IsV X p s then (if s+hP D p ∈ D.host.TT then al L a s/(p : ℝ) else minCredit X a b p j s 1)
      else (if s+hP D p ∈ D.host.TT then posDemand X a b p j s 1 else 0) := by
  have h := excl_one_iff hc hn s
  by_cases ht : s+hP D p ∈ D.host.TT <;> by_cases hv : IsV X p s
  · simpa [first,h.mpr ht,hv,ht,posDemand,minCredit] using max_add_min_eq (al L a s/(p : ℝ)) (capU X b p j s 1)
  · simp [first,h.mpr ht,hv,ht]
  · simp [first,h.not.mpr ht,hv,ht]
  · simp [first,h.not.mpr ht,hv,ht]

theorem odd_head_interval (q u : ℝ) (hq2 : 2 ≤ q) (w : ℕ → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hwu : ∀ e, w e ≤ u/q^e) :
    w 1 ≤ (∑' e, if Odd e then w e else 0) ∧
    (∑' e, if Odd e then w e else 0) ≤ w 1 + u/(q*(q^2-1)) := by
  let f (e : ℕ) := if Odd e then w e else 0
  let g (e : ℕ) := if Odd e then u/q^e else 0
  let spike (e : ℕ) := if e = 1 then g 1 - f 1 else 0
  have hf : Summable f := summable_if_of_le q u hq2 _ Odd hw hwu
  have hg : Summable g := summable_odd q u hq2 Odd
  have hs1 : HasSum spike (g 1 - f 1) := hasSum_ite_eq 1 _
  have heq : f 1 = w 1 := by simp [f]
  have hsingle := hf.le_tsum 1 (fun e _ => by dsimp [f]; split_ifs; exact hw e; exact le_rfl)
  have htail := Summable.tsum_le_tsum (f := fun e => f e + spike e) (g := g) (fun e => by
    by_cases he : e=1
    · subst e; simp [spike]
    · simp only [spike,if_neg he,add_zero,f,g]; split_ifs
      · exact hwu e
      · exact le_rfl) (hf.add hs1.summable) hg
  rw [hf.tsum_add hs1.summable,hs1.tsum_eq] at htail
  have hg1 : g 1 = u/q := by simp [g]
  have hval : (∑' e, g e) = q/(q^2-1)*u := tsum_odd q u hq2 Odd (fun _ => Iff.rfl)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hpq : 0 < q^2-1 := by nlinarith
  have he : q/(q^2-1)*u - u/q = u/(q*(q^2-1)) := by field_simp; ring
  change _ ≤ ∑' e, f e ∧ (∑' e, f e) ≤ _ + u/(q*(q^2-1))
  exact ⟨heq ▸ hsingle,by linarith only [htail,hg1,heq,hval,he]⟩

theorem minima_interval (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    minCredit X a b p j s 1 ≤ minima X a b p j s ∧
    minima X a b p j s ≤ minCredit X a b p j s 1 + al L a s / ((p : ℝ)*((p : ℝ)^2-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨ha,hcap⟩ := source_nonneg X P hW p hj hs
  exact odd_head_interval (p : ℝ) (al L a s) hp2 (minCredit X a b p j s)
    (fun e => le_min (div_nonneg ha (by positivity)) (hcap e)) (fun _ => min_le_left ..)

def firstBase (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  if Excl D p s 1 then 0 else posDemand X a b p j s 1

def firstPremium (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  max 0 ((∑ s ∈ topsOn X p t0, first X a b p j s) - Pr X K b p j t0 -
    max 0 (dl X K p t0 - ∑ s ∈ topsOn X p t0, firstBase X a b p j s))

theorem row_tail (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT) :
    let C := excluded X a b p j s + if IsV X p s then minima X a b p j s else 0
    let B := kept X a b p j s
    let C1 := first X a b p j s
    let B1 := firstBase X a b p j s
    B1 ≤ B ∧ C1 ≤ C ∧ B+C ≤ B1+C1 + al L a s / ((p : ℝ)*((p : ℝ)^2-1)) := by
  dsimp only
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨ha,hcap⟩ := source_nonneg X P hW p hj hs
  let f := posDemand X a b p j s
  have hn (e : ℕ) : 0 ≤ f e := le_max_left ..
  have hle (e : ℕ) : f e ≤ al L a s / (p : ℝ)^e := max_le (div_nonneg ha (by positivity)) (sub_le_self _ (hcap e))
  have hfirst (Q : ℕ → Prop) [DecidablePred Q] :
      (if Q 1 then f 1 else 0) ≤ ∑' e, if Q e then f e else 0 :=
    (summable_if_of_le (p : ℝ) (al L a s) hp2 f Q hn hle).le_tsum 1
      (fun e _ => by split_ifs; exact hn e; exact le_rfl)
  have hB := hfirst (fun e => Odd e ∧ ¬ Excl D p s e)
  have hC := hfirst (Excl D p s)
  have hmi := (minima_interval X P hW hp hj hs).1
  have Bineq : firstBase X a b p j s ≤ kept X a b p j s := by
    simpa [firstBase,kept,ite_not,f] using hB
  have Cineq : (if Excl D p s 1 then f 1 else 0) ≤ excluded X a b p j s := hC
  have hheads : firstBase X a b p j s + first X a b p j s =
      f 1 + if IsV X p s then minCredit X a b p j s 1 else 0 := by
    unfold firstBase first
    by_cases he : Excl D p s 1 <;> simp [he,f]
  refine ⟨Bineq,?_,?_⟩
  · unfold first
    apply add_le_add Cineq
    by_cases he : IsV X p s <;> simp [he,hmi]
  · rw [hheads]
    by_cases hv : IsV X p s
    · rw [if_pos hv,if_pos hv]
      have hbig := column_partition X P hW hp hj hs
      have hone : f 1 + minCredit X a b p j s 1 = al L a s / (p : ℝ) := by
        simpa [f,posDemand,minCredit] using max_add_min_eq (al L a s/(p : ℝ)) (capU X b p j s 1)
      rw [hone,←add_assoc,hbig]
      have hden : 0 < (p : ℝ)^2 - 1 := by nlinarith
      unfold gam
      apply le_of_eq
      field_simp
      ring
    · rw [if_neg hv,if_neg hv,add_zero,add_zero,demand_split X P hW hp hj hs]
      exact (odd_head_interval (p : ℝ) (al L a s) hp2 f hn hle).2

/-- A common error bound for both clamps. Each missing unit of credit or retained demand occurs once. -/
theorem premium_stability (C C1 B B1 price loss tail : ℝ) (hc : C1 ≤ C) (hb : B1 ≤ B)
    (ht : B+C ≤ B1+C1+tail) :
    max 0 (C1-price-max 0 (loss-B1)) ≤ max 0 (C-price-max 0 (loss-B)) ∧
    max 0 (C-price-max 0 (loss-B)) ≤ max 0 (C1-price-max 0 (loss-B1)) + tail := by
  have hcl := max_le_max_left (0 : ℝ) (sub_le_sub_left hb loss)
  have hz := le_max_left 0 (loss-B)
  have ho := le_max_right 0 (loss-B)
  have hrev : max 0 (loss-B1) ≤ max 0 (loss-B) + (B-B1) := max_le (by linarith) (by linarith)
  constructor
  · exact max_le_max_left _ (by linarith)
  · apply max_le
    · linarith [le_max_left 0 (C1-price-max 0 (loss-B1))]
    · linarith [le_max_right 0 (C1-price-max 0 (loss-B1))]

theorem orbit_tail_budget (X : Inst D L) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    let B := ∑ s ∈ topsOn X p t0, kept X a b p j s
    let C := credit X a b p j t0
    let B1 := ∑ s ∈ topsOn X p t0, firstBase X a b p j s
    let C1 := ∑ s ∈ topsOn X p t0, first X a b p j s
    B1 ≤ B ∧ C1 ≤ C ∧ B+C ≤ B1+C1+∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1)) := by
  let T := topsOn X p t0
  let C (s : HH D) := excluded X a b p j s + if IsV X p s then minima X a b p j s else 0
  have hC : (∑ s ∈ T, C s) = credit X a b p j t0 := by
    unfold credit
    rw [Finset.sum_filter]
    exact Finset.sum_add_distrib
  have hrow (s : HH D) (hs : s ∈ T) := row_tail X P hW hp hj (Finset.mem_filter.mp hs).1
  have Bineq := Finset.sum_le_sum (s := T) (fun s hs => (hrow s hs).1)
  have Cineq : (∑ s ∈ T, first X a b p j s) ≤ ∑ s ∈ T, C s := Finset.sum_le_sum (fun s hs => (hrow s hs).2.1)
  have total := Finset.sum_le_sum (s := T) (fun s hs => (hrow s hs).2.2)
  change (∑ s ∈ T, (kept X a b p j s + C s)) ≤ _ at total
  have hlhs : (∑ s ∈ T, (kept X a b p j s + C s)) = (∑ s ∈ T, kept X a b p j s) + ∑ s ∈ T, C s := Finset.sum_add_distrib
  rw [hlhs,hC] at total
  simp only [Finset.sum_add_distrib] at total
  rw [hC] at Cineq
  exact ⟨Bineq,Cineq,total⟩

theorem actual_premium_interval (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    firstPremium X K a b p j t0 ≤ improvement X K a b p j t0 ∧
    improvement X K a b p j t0 ≤ firstPremium X K a b p j t0 +
      ∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1)) := by
  have hB : -g0 X K a b p j t0 = dl X K p t0 - ∑ s ∈ topsOn X p t0, kept X a b p j s := by
    unfold g0
    change -((∑ s ∈ topsOn X p t0, kept X a b p j s)-_) = _
    ring
  obtain ⟨Bineq,Cineq,total⟩ := orbit_tail_budget X P hW hp hj t0
  unfold firstPremium improvement
  rw [hB]
  exact premium_stability _ _ _ _ _ _ _ Cineq Bineq total

/-- Above the cubic threshold all excluded positive demand is exactly first-exponent demand;
only the even-source minima can contribute to the remaining credit. -/
theorem bulk_credit_interval (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (hp3 : 2*L.sc.X' ≤ (p : ℝ)^3) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    (∑ s ∈ topsOn X p t0, first X a b p j s) ≤ credit X a b p j t0 ∧
    credit X a b p j t0 ≤ (∑ s ∈ topsOn X p t0, first X a b p j s) +
      ∑ s ∈ (topsOn X p t0).filter (IsV X p), al L a s/((p : ℝ)*((p : ℝ)^2-1)) := by
  let T := topsOn X p t0
  have hEx : (∑ s ∈ T, excluded X a b p j s) =
    ∑ s ∈ T, if Excl D p s 1 then posDemand X a b p j s 1 else 0 :=
    Finset.sum_congr rfl (fun s hs => excluded_eq_first X P hW hp hp3 hj (Finset.mem_filter.mp hs).1)
  have hhead : (∑ s ∈ T, first X a b p j s) = (∑ s ∈ T, if Excl D p s 1 then posDemand X a b p j s 1 else 0) +
    ∑ s ∈ T.filter (IsV X p), minCredit X a b p j s 1 := by
    unfold first
    rw [Finset.sum_add_distrib,Finset.sum_filter]
  have hlim (s : HH D) (hs : s ∈ T.filter (IsV X p)) := minima_interval X P hW hp hj (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have hlow := Finset.sum_le_sum (fun s hs => (hlim s hs).1)
  have hh := Finset.sum_le_sum (fun s hs => (hlim s hs).2)
  rw [Finset.sum_add_distrib] at hh
  rw [show topsOn X p t0 = T from rfl,hhead]
  unfold credit
  change _ ≤ (∑ s ∈ T, _) + (∑ s ∈ T.filter (IsV X p), _) ∧ _ ≤ _
  rw [hEx]
  constructor <;> linarith

/-- This is the same premium whose lift sum is rounded up in the source interaction penalty. -/
theorem sv_premium (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) (t0 : HH D) : Sv X K a b p t0 = ((⌈∑ j ∈ SizeData₂.lifts D, improvement X K a b p j t0⌉ : ℤ) : ℝ) := by
  unfold Sv
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have h := raw_difference X K P hW hp hj t0
  unfold improvement
  congr 1
  simp only [max_def]
  split_ifs <;> linarith

/-- The served row uses its surviving demand as baseline, then adds the positive excess of credit over price before the final zero floor. -/
theorem served_value (X : Inst D L) (K : Consts) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    max (gU X K a b p j t0-Pr X K b p j t0) (max (g0 X K a b p j t0) 0) =
      max 0 (g0 X K a b p j t0 + max 0 (credit X a b p j t0 - Pr X K b p j t0)) := by
  have h := raw_difference X K P hW hp hj t0
  simp only [max_def]
  split_ifs <;> linarith

def firstServed (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  max 0 ((∑ s ∈ topsOn X p t0, firstBase X a b p j s) - dl X K p t0 +
    max 0 ((∑ s ∈ topsOn X p t0, first X a b p j s) - Pr X K b p j t0))

/-- Combined first-exponent error for the actual local summand of gainP. -/
theorem actual_served_interval (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    let realGain := max (gU X K a b p j t0-Pr X K b p j t0) (max (g0 X K a b p j t0) 0)
    firstServed X K a b p j t0 ≤ realGain ∧ realGain ≤ firstServed X K a b p j t0 +
      ∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1)) := by
  dsimp only
  rw [served_value X K P hW hp hj t0]
  obtain ⟨hb,hc,ht⟩ := orbit_tail_budget X P hW hp hj t0
  let B := ∑ s ∈ topsOn X p t0, kept X a b p j s
  let C := credit X a b p j t0
  let B1 := ∑ s ∈ topsOn X p t0, firstBase X a b p j s
  let C1 := ∑ s ∈ topsOn X p t0, first X a b p j s
  let price := Pr X K b p j t0
  let loss := dl X K p t0
  let tail := ∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1))
  change B1 ≤ B at hb
  change C1 ≤ C at hc
  change B+C ≤ B1+C1+tail at ht
  change max 0 (B1-loss+max 0 (C1-price)) ≤ max 0 (B-loss+max 0 (C-price)) ∧ _
  change _ ∧ max 0 (B-loss+max 0 (C-price)) ≤ max 0 (B1-loss+max 0 (C1-price)) + tail
  have h1 := max_le_max_left (0 : ℝ) (sub_le_sub_right hc price)
  have h2 : max 0 (C-price) ≤ max 0 (C1-price)+(C-C1) :=
    max_le (by linarith [le_max_left 0 (C1-price)]) (by linarith [le_max_right 0 (C1-price)])
  constructor
  · exact max_le_max_left _ (by linarith)
  · exact max_le (by linarith [le_max_left 0 (B1-loss+max 0 (C1-price))])
      (by linarith [le_max_right 0 (B1-loss+max 0 (C1-price))])

/-- A signed error interval can certify which branch wins before the positive part is taken. -/
theorem decision_interval (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    let B1 := ∑ s ∈ topsOn X p t0, firstBase X a b p j s
    let C1 := ∑ s ∈ topsOn X p t0, first X a b p j s
    let tail := ∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1))
    let score := gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0
    let score1 := C1 - Pr X K b p j t0 - max 0 (dl X K p t0 - B1)
    score1 ≤ score ∧ score ≤ score1+tail := by
  obtain ⟨hb,hc,ht⟩ := orbit_tail_budget X P hW hp hj t0
  let B := ∑ s ∈ topsOn X p t0, kept X a b p j s
  let C := credit X a b p j t0
  let B1 := ∑ s ∈ topsOn X p t0, firstBase X a b p j s
  let C1 := ∑ s ∈ topsOn X p t0, first X a b p j s
  let price := Pr X K b p j t0
  let loss := dl X K p t0
  let tail := ∑ s ∈ topsOn X p t0, al L a s / ((p : ℝ)*((p : ℝ)^2-1))
  change B1 ≤ B at hb
  change C1 ≤ C at hc
  change B+C ≤ B1+C1+tail at ht
  have heq : gU X K a b p j t0 - price - max (g0 X K a b p j t0) 0 = C-price-max 0 (loss-B) := by
    have hx := raw_difference X K P hW hp hj t0
    change gU X K a b p j t0 - price - (B-loss) = C-price at hx
    change gU X K a b p j t0 - price - max (B-loss) 0 = _
    simp only [max_def]
    split_ifs <;> linarith
  dsimp only
  rw [heq]
  change C1-price-max 0 (loss-B1) ≤ C-price-max 0 (loss-B) ∧ C-price-max 0 (loss-B) ≤ C1-price-max 0 (loss-B1)+tail
  have hcl := max_le_max_left (0 : ℝ) (sub_le_sub_left hb loss)
  have hz := le_max_left 0 (loss-B)
  have ho := le_max_right 0 (loss-B)
  have hrev : max 0 (loss-B1) ≤ max 0 (loss-B) + (B-B1) := max_le (by linarith) (by linarith)
  constructor <;> linarith

/-- A single exponent cutoff suffices for all retained rows at this scale and prime. -/
theorem cutoff_exists (s : Scale) {p : ℕ} (hp : p.Prime) : ∃ N : ℕ, 2*s.a ≤ (p : ℝ)^N := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (2*s.a) (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  exact ⟨N,hN.le⟩

theorem demand_zero_after (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT)
    {N e : ℕ} (hN : 2*L.sc.a ≤ (p : ℝ)^N) (he : N ≤ e) : posDemand X a b p j s e = 0 := by
  obtain ⟨_,_,_,hcg,hSc⟩ := base P
  have hk := kaJ_le P j hj
  have ha := (a_bounds P hW hs).2.1
  have hf := fill_ge_one X P hW j (partner D p s e)
  have hcap : 1 ≤ capU X b p j s e := by unfold capU fillG; linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsupply : al L a s/(p : ℝ)^e ≤ 1 := by
    apply (div_le_one (pow_pos (by exact_mod_cast hp.pos : (0 : ℝ)<p) _)).mpr
    have hden := hN.trans (pow_le_pow_right₀ hp1 he)
    unfold al
    linarith
  exact max_eq_left (sub_nonpos.mpr (hsupply.trans hcap))

/-- Given a cutoff certificate and witness inputs, the three column series reduce exactly to finite sums. -/
theorem finite_column (X : Inst D L) (P : ParameterChoice' D L) {a b : HH D → ℤ} (hW : InWin L a b)
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {s : HH D} (hs : s ∈ D.host.TT)
    {N : ℕ} (hN : 2*L.sc.a ≤ (p : ℝ)^N) :
    let K0 := ∑ e ∈ Finset.range N, if Odd e ∧ ¬ Excl D p s e then posDemand X a b p j s e else 0
    let EX := ∑ e ∈ Finset.range N, if Excl D p s e then posDemand X a b p j s e else 0
    kept X a b p j s = K0 ∧ excluded X a b p j s = EX ∧ minima X a b p j s = gam p * al L a s - (K0+EX) := by
  have trunc (Q : ℕ → Prop) [DecidablePred Q] :
      (∑' e, if Q e then posDemand X a b p j s e else 0) = ∑ e ∈ Finset.range N, if Q e then posDemand X a b p j s e else 0 := by
    apply tsum_eq_sum
    intro e he
    have hzero := demand_zero_after X P hW hp hj hs hN (Nat.le_of_not_gt (fun h => he (Finset.mem_range.mpr h)))
    simp [hzero]
  have hB := trunc (fun e => Odd e ∧ ¬ Excl D p s e)
  have hC := trunc (Excl D p s)
  refine ⟨hB,hC,?_⟩
  have hpart := column_partition X P hW hp hj hs
  unfold excluded kept at hpart
  rw [hB,hC] at hpart
  linarith only [hpart]

end Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit

#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.source_nonneg
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.demand_split
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.column_partition
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.raw_difference
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.high_charge
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.served_max
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.gainP_split
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.excl_one_iff
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.excluded_deep_zero
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.excluded_eq_first
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.first_directed
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.odd_head_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.minima_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.row_tail
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.premium_stability
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.orbit_tail_budget
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.actual_premium_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.bulk_credit_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.sv_premium
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.served_value
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.actual_served_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.decision_interval
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.cutoff_exists
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.demand_zero_after
#print axioms Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit.finite_column
