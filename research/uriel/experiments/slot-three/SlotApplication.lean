import RankZero
import CyclotomicTransport
import FieldModel
import PrescribedPartB
import ZeroLift

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
open Formalism.ConjugateSelfDual
open UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

namespace SlotThree

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Use the same named center at every cutoff where Part B requests its finite set. -/
noncomputable def weightsAt (s : ℚ_[3]) (Z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Z).filter (fun e : ℕ => ‖s - (e : ℚ_[3])‖ < (3 : ℝ) ^ (-(Nat.log 3 Z : ℤ)))

theorem card_weightsAt (s : ℚ_[3]) (Z : ℕ) : (weightsAt s Z).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨har, hnear⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbr, hnear'⟩ := Finset.mem_filter.mp hb
  exact near1 3 ℚ_[3] s Z a b (Finset.mem_Icc.mp har).1 (Finset.mem_Icc.mp har).2
    (Finset.mem_Icc.mp hbr).1 (Finset.mem_Icc.mp hbr).2 hnear hnear'

theorem weightsAt64 (s : ℚ_[3]) : weightsAt s 64 = weights s := rfl

/-- Fix one generator and the legitimate lift [0] for its action on this field's tower module. -/
theorem common_lift (h : TowerClassHyp) :
    ∃ γ : G L Ω, IsGen 3 ⊤ γ ∧
      (∃ π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] XP 3 L, Function.Surjective π ∧
        ∀ v, π ((0 : Matrix (Fin 1) (Fin 1) ℤ_[3]).mulVec v) =
          (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 0 ∧ ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 1 ∧
      Certified 0 ∧ weightsAt 0 64 = ∅ ∧ Certified 1 ∧ weightsAt 1 64 = {1} := by
  obtain ⟨γ, hg, _, _⟩ := UpperTheory.V.PropA.genLevel 3 L muThree
  obtain ⟨matrix, _, ball0, ball1, _, _⟩ := same_lift_opposite (tower_module_zero h)
    (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ) (cycZ L Ω 3 γ : ℤ_[3])
  obtain ⟨⟨v0, w0⟩, ⟨v1, w1⟩⟩ := certified_one h
  exact ⟨γ, hg, matrix, ball0, ball1, v0, w0, v1, w1⟩

/-- The same lift and opposite certifications under the usual cyclotomic class-group condition. -/
theorem standard_common_lift (h : ∀ n : ℕ, 2 ≤ n →
    ¬ 3 ∣ Nat.card (ClassGroup (𝓞 (CyclotomicTransport.Standard n)))) :
    ∃ γ : G L Ω, IsGen 3 ⊤ γ ∧
      (∃ π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] XP 3 L, Function.Surjective π ∧
        ∀ v, π ((0 : Matrix (Fin 1) (Fin 1) ℤ_[3]).mulVec v) =
          (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 0 ∧ ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 1 ∧
      Certified 0 ∧ weightsAt 0 64 = ∅ ∧ Certified 1 ∧ weightsAt 1 64 = {1} :=
  common_lift (CyclotomicTransport.all_layers_iff.mpr h)

/-- The identified field model and its named arithmetic witnesses flow through
    the original odd-prime height estimate at the same cap and the same center. -/
theorem partB_for_center (h : TowerClassHyp) (s : ℚ_[3]) (CK : ℝ) (hCK : 0 < CK) (hK : LemmaK CK)
    (J Ct eps A1 : ℝ) (hJ : 0 < J) (hCt : 0 ≤ Ct) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X : ℝ,
      ∃ Exc : Finset ℕ, Exc = weightsAt s ⌊X ^ Ct⌋₊ ∧ Exc.card ≤ 1 ∧
        ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
          ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (AbF.cyc 3) L₀' →
            ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer 3 (jZero 3 1) L₀' L₁ →
              VVat 3 L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  exact partB_prescribed CK hCK hK 3 1 (by decide) (AbF.cyc 3)
    FieldModel.hasMu L FieldModel.fieldModel (actualABound s (any_center h s))
    1 (weightsAt s) (fun Z => firstBound_of_card h Z _ (card_weightsAt s Z))
    J Ct eps A1 hJ hCt heps

end SlotThree
