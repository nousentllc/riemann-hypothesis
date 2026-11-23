import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

namespace CoherentFields

/-- Later cutoffs can discard old labels and introduce new ones above the old range. -/
def OnOldRange (E : ℕ → Finset ℕ) : Prop :=
  ∀ u v e : ℕ, u ≤ v → e ≤ u → e ∈ E v → e ∈ E u

noncomputable def picks (l : ℕ) (K : Type) [NormedField K] {r : ℕ}
    (s : Fin r → K) (Z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Z).filter (fun e : ℕ =>
    ∃ i, ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)))

theorem mem_picks {l : ℕ} {K : Type} [NormedField K] {r : ℕ} {s : Fin r → K} {Z e : ℕ} :
    e ∈ picks l K s Z ↔ 1 ≤ e ∧ e ≤ Z ∧
      ∃ i, ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)) := by
  classical
  simp only [picks, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem picks_cohere {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K]
    {r : ℕ} (s : Fin r → K) : OnOldRange (picks l K s) := by
  intro u v e huv heu he
  rcases mem_picks.mp he with ⟨hp,_,i,hi⟩
  refine mem_picks.mpr ⟨hp,heu,i,hi.trans_le ?_⟩
  have h1 : (1:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  apply zpow_le_zpow_right₀ h1
  exact neg_le_neg (by exact_mod_cast Nat.log_mono_right huv)

/-- Freeze precisely one tuple of original cohomological witnesses, then compute all its
    finite-cutoff sets. These imply the actual numerical cohomology predicate at every Z. -/
theorem coherentFirst {l R : ℕ} [Fact l.Prime] {L : Type} [Field L]
    (h : ABound l R L) :
    ∃ (c : ℕ) (E : ℕ → Finset ℕ), (∃ ζ : L, IsPrimitiveRoot ζ (l^c)) ∧
      (∀ Z, FirstBound l R c L Z (E Z)) ∧ OnOldRange E := by
  classical
  obtain ⟨⟨K, _, _, _, c, r, s, hr, hζ, hb⟩, _⟩ := h
  refine ⟨c,picks l K s,hζ,fun Z => ?_,picks_cohere s⟩
  let near (i : Fin r) := (Finset.Icc 1 Z).filter (fun e : ℕ =>
    ‖s i - (e:K)‖ < (l:ℝ) ^ (-(Nat.log l Z : ℤ)))
  have hsup : picks l K s Z = Finset.univ.biUnion near := by
    ext e
    simp only [mem_picks, Finset.mem_biUnion, Finset.mem_univ, true_and, near,
      Finset.mem_filter, Finset.mem_Icc]
    aesop
  constructor
  · have hone : ∀ i, (near i).card ≤ 1 := by
      intro i
      apply Finset.card_le_one.mpr
      intro a ha b hb'
      simp only [near, Finset.mem_filter, Finset.mem_Icc] at ha hb'
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb'.1.1 hb'.1.2 ha.2 hb'.2
    rw [hsup]
    calc
      (Finset.univ.biUnion near).card ≤ ∑ i, (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin r, 1 := Finset.sum_le_sum (fun i _ => hone i)
      _ = r := by simp
      _ ≤ R := hr
  · intro e hp heZ hne m F _ _ _ hF
    have hfar : ∀ i, (l:ℝ)^(-(Nat.log l Z : ℤ)) ≤ ‖s i - (e:K)‖ := by
      intro i
      exact le_of_not_gt (fun hnear => hne (mem_picks.mpr ⟨hp,heZ,i,hnear⟩))
    exact (hb e hp m F hF (Nat.log l Z) hfar).trans (by gcongr)

/-- At a fixed finite set of nominated labels, only exact centers persist forever:
    no rate in l or r is asserted for the cutoff. -/
theorem stabilizes {l : ℕ} [Fact l.Prime] {K : Type} [NormedField K]
    {r : ℕ} (s : Fin r → K) (B : ℕ) :
    ∃ Z₀ : ℕ, ∀ Z ≥ Z₀, ∀ e : ℕ, 1 ≤ e → e ≤ B →
      (e ∈ picks l K s Z ↔ ∃ i, s i = (e : K)) := by
  classical
  have hl := (Fact.out : l.Prime).one_lt
  have hp : (1:ℝ) < l := by exact_mod_cast hl
  have sep : ∀ (e : Fin (B+1)) (i : Fin r), ∃ n : ℕ, s i ≠ (e.val : K) →
      ((l:ℝ)⁻¹)^n ≤ ‖s i - (e.val : K)‖ := by
    intro e i
    by_cases h : s i = (e.val : K)
    · exact ⟨0,fun hx => (hx h).elim⟩
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr (sub_ne_zero.mpr h))
      (inv_lt_one_of_one_lt₀ hp)
    exact ⟨n,fun _ => hn.le⟩
  choose n hn using sep
  let M := ∑ e, ∑ i, n e i
  have hiM (e : Fin (B+1)) (i : Fin r) : n e i ≤ M := by
    exact (Finset.single_le_sum (fun (z : Fin r) _ => Nat.zero_le (n e z)) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun (z : Fin (B+1)) _ => Nat.zero_le (∑ j, n z j)) (Finset.mem_univ e))
  refine ⟨max B (l^M),fun Z hZ e he hB => ?_⟩
  have heZ := hB.trans ((le_max_left _ _).trans hZ)
  constructor
  · intro hex
    obtain ⟨_,_,i,hi⟩ := mem_picks.mp hex
    refine ⟨i,?_⟩
    by_contra ne
    let f : Fin (B+1) := ⟨e,by omega⟩
    have hlog := (hiM f i).trans (Nat.le_log_of_pow_le hl ((le_max_right _ _).trans hZ))
    have hpow : (l:ℝ)^(-(Nat.log l Z : ℤ)) ≤ ((l:ℝ)⁻¹)^(n f i) := by
      rw [inv_pow, ← zpow_natCast (l:ℝ) (n f i), ← zpow_neg]
      apply zpow_le_zpow_right₀ hp.le
      exact neg_le_neg (by exact_mod_cast hlog)
    exact (not_lt_of_ge (hpow.trans (hn f i ne))) hi
  · rintro ⟨i,hei⟩
    refine mem_picks.mpr ⟨he,heZ,i,?_⟩
    rw [hei, sub_self, norm_zero]
    exact zpow_pos (by positivity) _

/-- The strict cutoff and allowance used by the active summands. -/
def Pass (E : Finset ℕ) (t : ℕ) (f : ℝ) : Prop :=
  ∀ e : ℕ, 1 ≤ e → e < t → e ∈ E → (e:ℝ) ≤ f

theorem mixedFill {E : ℕ → Finset ℕ} (h : OnOldRange E)
    {u v ta tx tb : ℕ} {A X B : ℝ} (huv : u ≤ v) (hcut : ta ≤ u+1)
    (ha : Pass (E u) ta A) (hb : Pass (E v) tb B)
    (hxt : tx ≤ tb) (hAX : A ≤ X) (hcross : B < (ta:ℝ)) :
    Pass (E v) tx X := by
  intro e he hea hm
  by_cases low : e < ta
  · exact (ha e he low (h u v e huv (by omega) hm)).trans hAX
  · have := hb e he (lt_of_lt_of_le hea hxt) hm
    have hta : ta ≤ e := by omega
    exact False.elim ((not_le_of_gt hcross) ((by exact_mod_cast hta : (ta:ℝ) ≤ e).trans this))

/-- Same l-adic digit depth permits exact transport at the actual two FirstBound
    constants. With a deeper digit one generally cannot lower the logarithmic cost. -/
theorem restrictAtEqualDepth {l R c u v : ℕ} [Fact l.Prime] {L : Type} [Field L]
    {E : Finset ℕ} (h : FirstBound l R c L v E) (huv : u ≤ v)
    (hd : Nat.log l u = Nat.log l v) : FirstBound l R c L u E := by
  refine ⟨h.1, fun e hp heU hne m F _ _ _ hf => ?_⟩
  rw [hd]
  exact h.2 e hp (heU.trans huv) hne m F hf

end CoherentFields
#print axioms CoherentFields.mem_picks
#print axioms CoherentFields.picks_cohere
#print axioms CoherentFields.coherentFirst
#print axioms CoherentFields.stabilizes
#print axioms CoherentFields.mixedFill
#print axioms CoherentFields.restrictAtEqualDepth
