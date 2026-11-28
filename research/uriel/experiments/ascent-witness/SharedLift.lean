import TowerResult

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
open Formalism.ConjugateSelfDual
open UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

namespace SlotThree.Complete

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Choose the generator and the surjective presentation of the zero matrix once. Each
subsequent label keeps them and gives the exact membership answers through its cutoff. -/
theorem shared_lift_all_labels :
    ∃ (γ : G L Ω) (π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] XP 3 L),
      IsGen 3 ⊤ γ ∧ Function.Surjective π ∧
      (∀ v, π ((0 : Matrix (Fin 1) (Fin 1) ℤ_[3]).mulVec v) =
        (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ∀ (Z : ℕ) (a : Fin (Z + 1)),
        ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) (a.val : ℤ_[3]) ∧
        SingleCenter (a.val : ℚ_[3]) ∧ SecondBound 3 1 L ∧
        FirstBound 3 1 1 L Z (weightsAt (a.val : ℚ_[3]) Z) ∧
        ∀ e : ℕ, 1 ≤ e → e ≤ Z → (e ∈ weightsAt (a.val : ℚ_[3]) Z ↔ a.val = e) := by
  obtain ⟨γ, hγ, ⟨π, hπ, hlift⟩, _⟩ := same_lift_unconditional
  refine ⟨γ, π, hγ, hπ, hlift, ?_⟩
  intro Z a
  obtain ⟨⟨hc, hsecond⟩, hfirst⟩ := all_labels_are_admissible Z a
  exact ⟨zero_root_any_center _ _, hc, hsecond, hfirst, AscentWitness.label_answers Z a⟩

#print axioms shared_lift_all_labels
end SlotThree.Complete
