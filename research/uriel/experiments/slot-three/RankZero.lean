import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
import SlotThree
import BaseField

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum
open UpperTheory.V.Tower UpperTheory.V.Two UpperTheory.V.PropA UpperTheory.V.Win
open UpperTheory.V.LDataCardLeFinrank

namespace SlotThree

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
abbrev L := BaseField.K
abbrev Ω := AlgebraicClosure L

/-- The external regular-prime class-number theorem, in the project's field model. -/
def TowerClassHyp : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ 3 ∣ Nat.card (ClassGroup (𝓞 (Fn L Ω 3 n)))

theorem hasRoot : ∃ ζ : L, IsPrimitiveRoot ζ 3 := by
  simpa using (BaseField.root_powers 1).mpr le_rfl

theorem source_cZero : UpperTheory.V.Tower.cZero 3 L = 1 := BaseField.maximal_level

theorem muThree : HasMuQ 3 L := by
  simpa [HasMuQ] using hasRoot

theorem quotient_bound (A : Type*) [CommGroup A] (h : ¬ 3 ∣ Nat.card A) :
    Nat.card (A ⧸ (powMonoidHom 3 : A →* A).range) ≤ 3 ^ 0 := by
  have hc : (Nat.card A).Coprime 3 := ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 h).symm
  have ht : (powMonoidHom 3 : A →* A).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hc.pow_left_bijective.surjective
  rw [ht]
  haveI := QuotientGroup.subsingleton_quotient_top (G := A)
  simp

theorem tower_module_zero (h : TowerClassHyp) : Subsingleton (XP 3 L) := by
  have hInf : XRk 3 1 (cycU 3 (⊤ : Subgroup (G L Ω))) 0 :=
    infRk L Ω 3 1 0 ⊤ one_ne_zero isClosed_univ fun n hn =>
      levelRk L Ω 3 n 0 hn (quotient_bound _ (h n hn))
  obtain ⟨π, onto⟩ := genOfRk L Ω 3 3 0 ⊤ isClosed_univ (hInf.of_one 3)
  exact ⟨fun a b => by
    obtain ⟨v, rfl⟩ := onto a
    obtain ⟨w, rfl⟩ := onto b
    exact congrArg π (Subsingleton.elim v w)⟩

/-- All layers and every positive weight, including weights inside a chosen ball. -/
theorem layer_zero (h : TowerClassHyp) (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁]
    (hl : IsLayer 3 m L L₁) : shaInv L₁ 3 e = 0 := by
  letI : Subsingleton (XP 3 L) := tower_module_zero h
  obtain ⟨γ, hgen, _, _⟩ := genLevel 3 L muThree
  have hd := descends 3 L muThree γ hgen
  rw [hd e he m L₁ hl]
  exact Module.length_eq_zero

/-- Expose the center in the first clause of ABound, with R=R'=c=1 and K=ℚ₃. -/
abbrev SingleCenter (s : ℚ_[3]) : Prop := AwayBound 3 1 L ℚ_[3] 1 1 (fun _ => s)

theorem any_center (h : TowerClassHyp) (s : ℚ_[3]) : SingleCenter s ∧ SecondBound 3 1 L := by
  constructor
  · intro e he m L₁ _ _ _ hl B _
    rw [layer_zero h e he m L₁ hl]
    exact zero_le
  · intro e he m L₁ _ _ _ hl L₂ _ _ _ _ Ω' _ _ _ D
    rw [layer_zero h e he m L₁ hl]
    exact zero_le

theorem actualABound (s : ℚ_[3]) (hs : SingleCenter s ∧ SecondBound 3 1 L) : ABound 3 1 L := by
  refine ⟨⟨ℚ_[3], inferInstance, inferInstance, inferInstance, 1, 1, fun _ => s, le_rfl, ?_, hs.1⟩, hs.2⟩
  simpa using hasRoot

theorem firstBound_of_card (h : TowerClassHyp) (Z : ℕ) (S : Finset ℕ) (hc : S.card ≤ 1) :
    FirstBound 3 1 1 L Z S := by
  refine ⟨hc, ?_⟩
  intro e he _ _ m L₁ _ _ _ hl
  rw [layer_zero h e he m L₁ hl]
  exact zero_le

/-- With one center, the union in the original `exc` proof is this single filter. -/
def weights (s : ℚ_[3]) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 64).filter (fun e : ℕ => ‖s - (e : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 64 : ℤ)))

theorem weight_iff (a e : ℕ) : e ∈ weights (a : ℚ_[3]) ↔
    1 ≤ e ∧ e ≤ 64 ∧ (81 : ℤ) ∣ (a : ℤ) - (e : ℤ) := by
  classical
  simp only [weights, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  simpa only [Int.cast_natCast] using
    and_congr_right (fun _ : 1 ≤ e => and_congr_right
      (fun _ : e ≤ 64 => integer_center_iff ℚ_[3] (a : ℤ) (e : ℤ)))

theorem zero_weights : weights 0 = ∅ := by
  ext e
  simpa only [Nat.cast_zero, Nat.zero_le, Finset.notMem_empty, iff_false] using
    (show ¬ e ∈ weights ((0 : ℕ) : ℚ_[3]) from fun h => by
      have := (weight_iff 0 e).mp h
      omega)

theorem singleton_weights (a : ℕ) (ha : 1 ≤ a) (hZ : a ≤ 64) : weights (a : ℚ_[3]) = {a} := by
  ext e
  rw [weight_iff, Finset.mem_singleton]
  omega

/-- Store the named center, the returned set and its two arithmetic obligations together. -/
def Certified (s : ℚ_[3]) : Prop :=
  (SingleCenter s ∧ SecondBound 3 1 L) ∧ FirstBound 3 1 1 L 64 (weights s)

theorem certified_opposite (h : TowerClassHyp) (a : ℕ) (ha : 1 ≤ a) (hZ : a ≤ 64) :
    (Certified 0 ∧ weights 0 = ∅) ∧ (Certified (a : ℚ_[3]) ∧ weights (a : ℚ_[3]) = {a}) := by
  have hs := singleton_weights a ha hZ
  exact ⟨⟨⟨any_center h 0, firstBound_of_card h _ _ (by simp [zero_weights])⟩, zero_weights⟩,
         ⟨⟨any_center h a, firstBound_of_card h _ _ (by simp [hs])⟩, hs⟩⟩

theorem certified_one (h : TowerClassHyp) :
    (Certified 0 ∧ weights 0 = ∅) ∧ (Certified 1 ∧ weights 1 = {1}) := by
  simpa using certified_opposite h 1 (by decide) (by decide)

end SlotThree
end
