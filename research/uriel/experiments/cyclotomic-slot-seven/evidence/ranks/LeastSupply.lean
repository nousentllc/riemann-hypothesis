import SuccessiveFields
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields SynchronizedSlots
noncomputable section
namespace Seven.Ranks

def ZeroRank (l : ℕ) (A : AbF) : Prop :=
  ∃ (_ : Fact l.Prime) (F : Type) (_ : Field F) (_ : NumberField F), IsAbField A F ∧ ABound l 0 F

theorem coherentLeast (wA wB : ℝ) (ha : wA < 11/20) (hb : wB < 4/5) :
    (∃ CK : ℝ, LemmaK CK) → FixedIn → TwoIn → ∃ K : BConst,
      1 ≤ K.CK ∧
      (∀ (l : ℕ) (A : AbF), ZeroRank l A → K.Rl l A = 0) ∧ ∀ Ct : ℝ, 1 ≤ Ct → Across K wA wB Ct := by
  rintro ⟨CK0, hK0⟩ hF hT
  classical
  have hCK1 : (1 : ℝ) ≤ max CK0 1 := le_max_right _ _
  have hCKpos : (0 : ℝ) < max CK0 1 := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaK (max CK0 1) := kmono CK0 _ (le_max_left _ _) hK0
  let P : ℕ → AbF → ℕ → Prop := fun l A R =>
    ∃ (_ : Fact l.Prime) (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField A L₀ ∧ ABound l R L₀
  let R0 : AbF → ℕ := fun M => Classical.choose (hT M)
  let Rl : ℕ → AbF → ℕ := fun l A => if h : ∃ R, P l A R then Nat.find h else 0
  refine ⟨BConst.mk R0 Rl (max CK0 1) hCKpos, hCK1, ?_, fun Ct hCt => ?_⟩
  · intro l A hz
    have hzero : P l A 0 := hz
    have hex : ∃ R, P l A R := ⟨0,hzero⟩
    change (if h : ∃ R, P l A R then Nat.find h else 0) = 0
    rw [dif_pos hex]
    exact Nat.le_zero.mp (Nat.find_min' hex hzero)
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
      have hRl : Rl l (L l) = Nat.find hP := by
        show (if h : ∃ R, P l (L l) R then Nat.find h else 0) = _
        rw [dif_pos hP]
      obtain ⟨_, L₀₀, _, _, hab0, hR0⟩ := Nat.find_spec hP
      obtain ⟨x0, hx0⟩ := coherentPartB wB hb CK hCKpos hK l (Nat.find hP) hl2 (L l) hmu L₀₀ hab0 hR0
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

end Seven.Ranks
end
#print axioms Seven.Ranks.coherentLeast
