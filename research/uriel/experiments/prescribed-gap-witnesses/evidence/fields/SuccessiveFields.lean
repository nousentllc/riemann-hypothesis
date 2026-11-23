import SynchronizedSlots

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
noncomputable section
namespace SynchronizedSlots

/-- Fixed odd tables precede even the pair; each even table precedes all outer
    cutoffs for that pair. The finite subsets at different cutoffs can differ. -/
def Across (K : BConst) (wA wB Ct : ℝ) : Prop :=
  ∀ (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF), OddPrimesWithRootsOfUnity B' L →
    ∀ eps A1 : ℝ, 0 < eps → eps < 1/52 → ∃ X0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t →
    ∃ EB : ℕ → ℕ → Finset ℕ, (∀ l ∈ B', OnOldRange (EB l)) ∧
      (∀ l ∈ B', ∀ Z, (EB l Z).card ≤ K.Rl l (L l)) ∧
    ∀ q d : ℕ, PrimePair M.m q d → ∃ EA : ℕ → Finset ℕ,
      OnOldRange EA ∧ (∀ Z, (EA Z).card ≤ K.R0 M) ∧ ∀ X ≥ X0,
      Real.log ((q:ℝ)*d) ≤ X^(eps/(4*K.J Ct eps M B' L)) →
      ∀ x, X^(1/(K.J Ct eps M B' L)) ≤ x → x ≤ X →
        ActiveSmall (wA*eps/K.CK) (EA ⌊X^Ct⌋₊) (t x) x →
        (∀ l ∈ B', ActiveSmall (wB*eps/K.CK) (EB l ⌊X^Ct⌋₊) (t x) x ∨
          BbAt K ({l} : Finset ℕ) L eps t x) →
        BaAt M eps e t q d x ∧ BbAt K B' L eps t x
theorem coherentJoint (wA wB : ℝ) (ha : wA < 11/20) (hb : wB < 4/5) :
    (∃ CK : ℝ, LemmaK CK) → FixedIn → TwoIn → ∃ K : BConst,
      1 ≤ K.CK ∧ ∀ Ct : ℝ, 1 ≤ Ct → Across K wA wB Ct := by
  rintro ⟨CK0, hK0⟩ hF hT
  classical
  have hCK1 : (1 : ℝ) ≤ max CK0 1 := le_max_right _ _
  have hCKpos : (0 : ℝ) < max CK0 1 := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaK (max CK0 1) := kmono CK0 _ (le_max_left _ _) hK0
  let P : ℕ → AbF → ℕ → Prop := fun l A R =>
    ∃ (_ : Fact l.Prime) (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField A L₀ ∧ ABound l R L₀
  let R0 : AbF → ℕ := fun M => Classical.choose (hT M)
  let Rl : ℕ → AbF → ℕ := fun l A => if h : ∃ R, P l A R then Classical.choose h else 0
  refine ⟨BConst.mk R0 Rl (max CK0 1) hCKpos, hCK1, fun Ct hCt => ?_⟩
  unfold Across
  intro M B' L hAux eps A1 heps heps'
  unfold OddPrimesWithRootsOfUnity at hAux
  have hCt0 : 0 < Ct := lt_of_lt_of_le one_pos hCt
  set CK : ℝ := max CK0 1 with hCKdef
  set R : ℕ := R0 M + ∑ l ∈ B', Rl l (L l) with hRdef
  set J : ℝ := 2 ^ (R + 2) * (2 * CK * Ct / eps) ^ R with hJdef
  have hJpos : 0 < J := by
    have : 0 < 2 * CK * Ct / eps := by positivity
    positivity
  obtain ⟨x0A, hA⟩ := coherentPartA wA ha CK hCKpos hK M (R0 M) J Ct eps A1 hJpos hCt0.le heps
  have hB : ∀ l ∈ B', ∃ x0 : ℝ, ∀ e t, admitted A1 Ct e t → ∃ E : ℕ → Finset ℕ,
      OnOldRange E ∧ (∀ Z, (E Z).card ≤ Rl l (L l)) ∧ ∀ X : ℝ, ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (wB * eps / CK) (E ⌊X ^ Ct⌋₊) (t x) x →
        ∀ (_ : Fact l.Prime) (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (L l) L₀' →
          ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁],
            IsLayer l (Nat.log l (Rl l (L l)) + 3) L₀' L₁ → VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
    intro l hl
    obtain ⟨hp, hl2, hmu⟩ := hAux l hl
    haveI : Fact l.Prime := ⟨hp⟩
    by_cases hex : ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField (L l) L₀
    · obtain ⟨L₀, _, _, hab⟩ := hex
      have hP : ∃ R, P l (L l) R := by
        obtain ⟨R', hR'⟩ := hF l hl2 (L l) hmu L₀ hab
        exact ⟨R', ⟨_, L₀, _, _, hab, hR'⟩⟩
      have hRl : Rl l (L l) = Classical.choose hP := by
        show (if h : ∃ R, P l (L l) R then Classical.choose h else 0) = _
        rw [dif_pos hP]
      obtain ⟨_, L₀₀, _, _, hab0, hR0⟩ := Classical.choose_spec hP
      obtain ⟨x0, hx0⟩ := coherentPartB wB hb CK hCKpos hK l (Classical.choose hP) hl2 (L l) hmu L₀₀ hab0 hR0
        J Ct eps A1 hJpos hCt0.le heps
      refine ⟨x0, fun e t hAdm => ?_⟩
      obtain ⟨Exc, coh, hcard, hx⟩ := hx0 e t hAdm
      refine ⟨Exc, coh, hRl ▸ hcard, fun X x hxx hlo hhi hg _ L₀' _ _ hab' L₁ _ _ _ hlay => ?_⟩
      rw [hRl] at hlay
      exact hx X x hxx hlo hhi hg L₀' hab' L₁ hlay
    · refine ⟨0, fun e t _ => ⟨fun _ => ∅, by intro u v e hu he h; simpa using h, by simp, ?_⟩⟩
      intro X x _ _ _ _ _ L₀' _ _ hab' _ _ _ _ _
      exact absurd ⟨L₀', _, _, hab'⟩ hex
  choose! f hf using hB
  set x1 : ℝ := max 1 (max x0A (∑ l ∈ B', |f l|)) with hx1def
  have hfle : ∀ l ∈ B', f l ≤ x1 := fun l hl =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hl).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hx0A : x0A ≤ x1 := (le_max_left _ _).trans (le_max_right _ _)
  have hx1pos : 0 ≤ x1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 2 (x1 ^ J), fun e t hAdm => ?_⟩
  have tables := fun l hl => hf l hl e t hAdm
  choose! g hg using tables
  refine ⟨g,fun l hl => (hg l hl).1,fun l hl => (hg l hl).2.1,?_⟩
  intro q d hqd
  obtain ⟨L₀, _, _, hTB, hAB⟩ := Classical.choose_spec (hT M) q d hqd
  obtain ⟨EA,coh,cap,hxA⟩ := hA e t hAdm q d hqd L₀ hTB hAB
  refine ⟨EA,coh,cap,?_⟩
  intro X hX hlog x hXlo hXhi hAact hBact
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXJ : x1 ^ J ≤ X := (le_max_right _ _).trans hX
  have hlow : x1 ≤ X ^ (1 / J) := by
    calc x1 = (x1 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx1pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx1pos _) hXJ (by positivity)
  refine ⟨hxA X hlog x (hx0A.trans (hlow.trans hXlo)) hXlo hXhi hAact, ?_⟩
  unfold BbAt
  intro l hl _ L₀' _ _ hab L₁ _ _ _ hlay
  rcases hBact l hl with hactive | hdirect
  · exact (hg l hl).2.2 X x ((hfle l hl).trans (hlow.trans hXlo)) hXlo hXhi
      hactive _ L₀' hab L₁ hlay
  · exact hdirect l (Finset.mem_singleton_self _) L₀' hab L₁ hlay

open IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal
  UpperTheory.V.Base UpperTheory.V.HV

/-- A predetermined gap with distinct earlier/later tests for the same arithmetic tables.
The numerical conditions are those of the later outer envelope. -/
theorem gapVAt (wA wB : ℝ) (K : BConst) (Ct eps : ℝ) (psi : PChar)
    (hCt : 1 ≤ Ct) (heps : 0 < eps) (heps52 : eps < 1/52)
    (hwA : 0 ≤ wA*eps/K.CK) (hwB : 0 ≤ wB*eps/K.CK)
    (hj : Across K wA wB Ct) (hp : PointHV) (hc : ThmBc Ct)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1:ℝ), PageN eps x (e x))
    (D : Finset ℕ) (direct : ∀ x ≥ (1:ℝ), BbAt K D (Lchi psi) eps (fun y => ⌊y^Ct⌋₊) x) :
    ∃ r₁ r₂ : ℕ, ∃ L X0 : ℝ, ∃ EB : ℕ → ℕ → Finset ℕ,
    (∀ l ∈ Bchi psi, OnOldRange (EB l)) ∧
    (∀ l ∈ Bchi psi, ∀ Z, (EB l Z).card ≤ K.Rl l (Lchi psi l)) ∧
    ∀ q d : ℕ, PrimePair psi.N q d → ∃ EA : ℕ → Finset ℕ,
    OnOldRange EA ∧ (∀ Z, (EA Z).card ≤ K.R0 (AbF.ofChar psi)) ∧
    ∀ (U X a b V : ℝ), 0 ≤ U → U ≤ X → X0 ≤ X → L ≤ a → a ≤ b →
    a ≤ U → X^(1/Jchi K Ct eps psi) ≤ a → b ≤ X →
    WinPair eps V q d → 2*X^Ct+1 < (q:ℝ) → 2*X^Ct+1 < (d:ℝ) →
    (∀ k ∈ [psi.N, ordC psi, pK psi, hStar psi, pOne psi, r₁, r₂], k < q ∧ k < d) →
    Real.log ((q:ℝ)*d) ≤ X ^ (eps/(4*Jchi K Ct eps psi)) →
    b^(wA*eps/K.CK) < (⌊a^Ct⌋₊ : ℝ) → b^(wB*eps/K.CK) < (⌊a^Ct⌋₊ : ℝ) →
    ActiveSmall (wA*eps/K.CK) (EA ⌊U^Ct⌋₊) ⌊a^Ct⌋₊ a →
    ActiveSmall (wA*eps/K.CK) (EA ⌊X^Ct⌋₊) ⌊b^Ct⌋₊ b →
    (∀ l ∈ Bchi psi, l ∉ D → ActiveSmall (wB*eps/K.CK) (EB l ⌊U^Ct⌋₊) ⌊a^Ct⌋₊ a) →
    (∀ l ∈ Bchi psi, l ∉ D → ActiveSmall (wB*eps/K.CK) (EB l ⌊X^Ct⌋₊) ⌊b^Ct⌋₊ b) →
    ∀ x, a ≤ x → x ≤ b → VAt psi eps Ct q d (e x) x := by
  let t : ℝ → ℕ := fun x => ⌊x^Ct⌋₊
  have ht := admissible_of_pageN heps heps52 hCt hpage
  have hct0 : 0 < Ct := by linarith
  have hJ : 0 < Jchi K Ct eps psi := BConst.J_pos K hct0 heps _ _ _
  obtain ⟨X0,hX0⟩ := hj (AbF.ofChar psi) (Bchi psi) (Lchi psi) (primeSetBoundData_of_primitiveChar psi) eps 4 heps heps52
  obtain ⟨EB,coB,capB,pairs⟩ := hX0 e t ht
  obtain ⟨C,r₁,r₂,hheight⟩ := heightAt hp K Ct hct0 psi
  obtain ⟨L,hL⟩ := fieldAt psi Ct C eps hCt heps heps52 hc e hpage
  refine ⟨r₁,r₂,max 2 L,X0,EB,coB,capB,?_⟩
  intro q d hpair
  obtain ⟨EA,coA,capA,hs⟩ := pairs q d hpair
  refine ⟨EA,coA,capA,?_⟩
  intro U X a b V hU huX hX hLa hab haU hlow hbX hw hq hd hlist hlog ca cb haA hbA haB hbB x hax hxb
  have ha2 : 2 ≤ a := (le_max_left 2 L).trans hLa
  have ha0 : 0 ≤ a := by linarith
  have floorMono {p z : ℝ} (h0 : 0 ≤ p) (hpz : p ≤ z) : ⌊p^Ct⌋₊ ≤ ⌊z^Ct⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow h0 hpz hct0.le)
  have hcut := (floorMono ha0 haU).trans (Nat.le_succ _)
  have uv := floorMono hU huX
  have xt := floorMono (ha0.trans hax) hxb
  have hactA := fillFromTwoCutoffs coA uv hcut haA hbA xt ha0 hax hwA ca
  have hactB : ∀ l ∈ Bchi psi, ActiveSmall (wB*eps/K.CK) (EB l ⌊X^Ct⌋₊) (t x) x ∨
      BbAt K ({l}:Finset ℕ) (Lchi psi) eps t x := by
    intro l hl
    by_cases hd : l ∈ D
    · right
      intro lp hmem hPrime
      have heq := Finset.mem_singleton.mp hmem
      subst lp
      exact @direct x (by linarith) l hd hPrime
    · exact Or.inl (fillFromTwoCutoffs (coB l hl) uv hcut (haB l hl hd) (hbB l hl hd) xt ha0 hax hwB cb)
  have hx := hs X hX hlog x (hlow.trans hax) (hxb.trans hbX) hactA hactB
  have hv := hheight eps 4 e t ht X x q d (ha2.trans hax) (hxb.trans hbX) hpair hq hd hlist hx.2
  have hlogx := hlog.trans (logs.2.1 _ eps X x hJ heps (by linarith) (hlow.trans hax))
  exact hL x (((le_max_right _ _).trans hLa).trans hax) V q d hw hpair hlogx hx.1 hv

end SynchronizedSlots
end
#print axioms SynchronizedSlots.coherentJoint
#print axioms SynchronizedSlots.gapVAt
