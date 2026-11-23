import SharedLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
open Formalism.HC UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower
open SlotThree

namespace GapFirst.Slot

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Direct certificate on every isomorphic realization of the identified base.
    The layer number, weight cutoff, and preselected ordinate are arbitrary. -/
theorem zeroOnModel (m t : ℕ) (F : Type) [Field F] [NumberField F]
    (hF : IsAbField (AbF.cyc 3) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 3 m F E)
    (B : ℝ) (hB : 0 ≤ B) : VVat 3 E t B := by
  obtain ⟨T, i1, i2, i3, hT⟩ := layerex 3 m (by decide) SlotThree.L SlotThree.muThree
  obtain ⟨f⟩ := abiso (AbF.cyc 3) SlotThree.L F SlotThree.FieldModel.fieldModel hF
  obtain ⟨g⟩ := layeriso 3 m (by decide) SlotThree.L F T E ⟨f⟩ hT hE
  apply vvat 3 t E (t : ℝ) 0 B (by norm_num) le_rfl (by simpa using hB)
  intro e he _
  rw [← shaInv_congr g, SlotThree.Complete.layer_invariant_zero e he m T hT]
  simp

/-- The remaining odd components of the *same* original weighted bound are
    necessary and sufficient, for the same K and every preassigned scale. -/
theorem eraseThree (K : BConst) (B' : Finset ℕ) (L' : ℕ → AbF)
    (hL : L' 3 = AbF.cyc 3) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) :
    BbAt K B' L' eps t x ↔ BbAt K (B'.erase 3) L' eps t x := by
  constructor
  · intro full l hl hp F i1 i2 hF E i3 i4 i5 hE
    exact full l (Finset.mem_of_mem_erase hl) F hF E hE
  · intro rest l hl hp F i1 i2 hF E i3 i4 i5 hE
    by_cases h : l = 3
    · subst l
      rw [hL] at hF
      exact zeroOnModel _ _ F hF E hE _ (Real.exp_pos _).le
    · exact rest l (Finset.mem_erase.mpr ⟨h, hl⟩) F hF E hE

theorem principalGap (a b : ℝ) (K : BConst) (eps : ℝ) (t : ℝ → ℕ) :
    (∀ x ∈ Set.Icc a b, BbAt K (Bchi PChar.one) (Lchi PChar.one) eps t x) ↔
    (∀ x ∈ Set.Icc a b, BbAt K ((Bchi PChar.one).erase 3) (Lchi PChar.one) eps t x) := by
  have hL : Lchi PChar.one 3 = AbF.cyc 3 := by simp [Lchi, PChar.one]
  exact forall_congr' fun x => forall_congr' fun _ => eraseThree K _ _ hL eps t x


/-- A single generator and lift allow every integral center, at all precisions. -/
theorem allCentersOneLift :
    ∃ (γ : G L Ω) (π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] XP 3 L),
      IsGen 3 ⊤ γ ∧ Function.Surjective π ∧
      (∀ v, π ((0 : Matrix (Fin 1) (Fin 1) ℤ_[3]).mulVec v) =
        (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ∀ s : ℤ_[3], ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) s ∧
        SingleCenter (s : ℚ_[3]) ∧ SecondBound 3 1 L ∧
        ∀ Z : ℕ, FirstBound 3 1 1 L Z (weightsAt (s : ℚ_[3]) Z) := by
  obtain ⟨γ, hγ, ⟨π, hπ, hlift⟩, _⟩ := SlotThree.Complete.same_lift_unconditional
  refine ⟨γ, π, hγ, hπ, hlift, ?_⟩
  intro s
  obtain ⟨hc, hb⟩ := SlotThree.any_center SlotThree.Complete.towerClass (s : ℚ_[3])
  exact ⟨SlotThree.zero_root_any_center _ _, hc, hb, fun Z =>
    SlotThree.firstBound_of_card SlotThree.Complete.towerClass Z _ (SlotThree.card_weightsAt _ _)⟩

theorem principalDirect (K : BConst) (eps : ℝ) (t : ℝ → ℕ) (x : ℝ) :
    BbAt K ({3} : Finset ℕ) (Lchi PChar.one) eps t x := by
  apply (eraseThree K _ _ (by simp [Lchi, PChar.one]) eps t x).2
  intro l hl
  simp at hl

#print axioms principalDirect
#print axioms allCentersOneLift

#print axioms zeroOnModel
#print axioms eraseThree
#print axioms principalGap

end GapFirst.Slot
