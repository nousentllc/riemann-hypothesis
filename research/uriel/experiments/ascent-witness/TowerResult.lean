import Transfer
import InertiaDescent
import UpstairsExtension
import HilbertNormal
import WitnessRecord

open NumberField GroundTheory.Global SlotThree SlotThree.NextLayer
open Ascent.Upstairs
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
open Formalism.ConjugateSelfDual
open UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
open ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

namespace SlotThree.Complete

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Obtain a nontrivial unramified elementary cover from a nonzero upstairs 3-class. -/
private theorem use_elementary_cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsTotallyComplex E] (hd : Module.finrank F E = 3)
    (close : ∀ (U : Type) [Field U] [NumberField U] [Algebra F U] [Algebra E U]
      [IsScalarTower F E U] [IsGalois F U], IsUnramifiedEverywhere E U →
      IsPGroup 3 Gal(U/F) → 3 < Nat.card Gal(U/F) → False)
    (bad : 3 ∣ Nat.card (ClassGroup (𝓞 E))) : False := by
  let Ω := AlgebraicClosure E
  let H := Ascent.Upstairs.H E Ω
  let : NumberField H := NumberField.of_module_finite E H
  let : IsGalois F H := _root_.Ascent.Direct.hilbert_galois F E Ω
  let U := Elementary E Ω
  let : NumberField U := NumberField.of_module_finite E U
  let : IsGalois F U := elementary_galois_downstairs E Ω F
  let : IsAbelianGalois E U := elementary_abelian E Ω
  obtain ⟨hp, hbig⟩ := Ascent.cover_group F E U hd (elementary_pgroup E Ω)
    (elementary_degree_pos E Ω bad)
  exact close U (elementary_unramified E Ω) hp hbig

/-- An everywhere-unramified abelian cubic forces three to divide the class number. -/
private theorem exclude_unramified_cubic (F U : Type) [Field F] [NumberField F] [Field U] [NumberField U] [Algebra F U]
    (base : ¬3 ∣ Nat.card (ClassGroup (𝓞 F)))
    (obstruction : ∃ M : IntermediateField F U, IsAbelianGalois F M ∧
      Module.finrank F M = 3 ∧ IsUnramifiedEverywhere F M) : False := by
  obtain ⟨M, hM, hdeg, hm⟩ := obstruction
  let _ := hM
  have hd := Ascent.unramified_degree_dvd F M hm
  rw [hdeg] at hd
  exact base hd
/-- A nonzero upstairs 3-class would yield an unramified cubic extension of the lower field. -/
theorem ascend (k : ℕ) (base : ¬3 ∣ Nat.card (ClassGroup (𝓞 (Lower k)))) :
    ¬3 ∣ Nat.card (ClassGroup (𝓞 (Upper k))) := by
  let _ := step_galois k
  let _ : IsTotallyComplex (Upper k) := totally_complex (k+1)
  apply use_elementary_cover (Lower k) (Upper k) (step_degree k)
  intro U _ _ _ _ _ _ hu hp hbig
  exact exclude_unramified_cubic (Lower k) U base
    (InertiaDescent.descend k U hu hbig (Ascent.cubic_quotient_of_proper hp))

theorem regular_layer (k : ℕ) : ¬3 ∣ Nat.card (ClassGroup (𝓞 (Lower k))) := by
  induction k with
  | zero =>
    rw [CyclotomicTransport.class_card 1 (by decide)]
    simpa [CyclotomicTransport.Standard] using BaseField.three_not_dvd_class_card
  | succ k ih => exact ascend k ih

theorem towerClass : TowerClassHyp := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact regular_layer k

theorem standard_layers : ∀ n : ℕ, 2 ≤ n →
    ¬ 3 ∣ Nat.card (ClassGroup (𝓞 (CyclotomicTransport.Standard n))) :=
  CyclotomicTransport.all_layers_iff.mp towerClass

theorem opposite_at_64 :
    (Certified 0 ∧ weights 0 = ∅) ∧ (Certified 1 ∧ weights 1 = {1}) :=
  certified_one towerClass

theorem all_labels_are_admissible (Z : ℕ) (a : Fin (Z+1)) :
    (SingleCenter (a.val : ℚ_[3]) ∧ SecondBound 3 1 L) ∧
    FirstBound 3 1 1 L Z (weightsAt (a.val : ℚ_[3]) Z) :=
  AscentWitness.admissible_label towerClass Z a

theorem layer_invariant_zero (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁]
    (hl : IsLayer 3 m L L₁) : shaInv L₁ 3 e = 0 :=
  layer_zero towerClass e he m L₁ hl

theorem norm_on_coinvariants_bijective (k : ℕ) :
    ∃ σ : Gal(Upper k / Lower k), (∀ τ, τ ∈ Subgroup.zpowers σ) ∧
      Function.Bijective (Ascent.normOnCoinvariants (Lower k) (Upper k) σ) :=
  Ascent.norm_equiv_of_regular_tower towerClass k

theorem fixed_class_divisibility : Ascent.FixedClassDivisibility :=
  Ascent.fixed_of_regular_tower towerClass

theorem coinvariant_norm_injective : Ascent.CoinvariantNormInjectivity :=
  Ascent.coinvariant_of_regular_tower towerClass

theorem fixed_class_count (k : ℕ) :
    Nat.card (Ascent.FixedClasses (Lower k) (Upper k)) = Nat.card (Ascent.Cl (Lower k)) :=
  Ascent.fixed_card_eq_lower towerClass k

theorem same_lift_unconditional :
    ∃ γ : G L Ω, IsGen 3 ⊤ γ ∧
      (∃ π : (Fin 1 → ℤ_[3]) →ₗ[ℤ_[3]] XP 3 L, Function.Surjective π ∧
        ∀ v, π ((0 : Matrix (Fin 1) (Fin 1) ℤ_[3]).mulVec v) =
          (xRep 3 3 (⊤ : Subgroup (G L Ω)) γ ^ (3 ^ 3 : ℕ)) (π v)) ∧
      ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 0 ∧ ZeroRootBall (cycZ L Ω 3 γ : ℤ_[3]) 1 ∧
      Certified 0 ∧ weightsAt 0 64 = ∅ ∧ Certified 1 ∧ weightsAt 1 64 = {1} :=
  common_lift towerClass

theorem partB_named_center (s : ℚ_[3]) (CK : ℝ) (hCK : 0 < CK) (hK : LemmaK CK)
    (J Ct eps A1 : ℝ) (hJ : 0 < J) (hCt : 0 ≤ Ct) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X : ℝ,
      ∃ Exc : Finset ℕ, Exc = weightsAt s ⌊X ^ Ct⌋₊ ∧ Exc.card ≤ 1 ∧
        ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
          ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (AbF.cyc 3) L₀' →
            ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer 3 (jZero 3 1) L₀' L₁ →
              VVat 3 L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) :=
  partB_for_center towerClass s CK hCK hK J Ct eps A1 hJ hCt heps

#print axioms layer_invariant_zero
#print axioms norm_on_coinvariants_bijective
#print axioms fixed_class_divisibility
#print axioms coinvariant_norm_injective
#print axioms fixed_class_count
#print axioms same_lift_unconditional
#print axioms partB_named_center
#print axioms ascend
#print axioms regular_layer
#print axioms towerClass
#print axioms standard_layers
#print axioms opposite_at_64
#print axioms all_labels_are_admissible
end
end SlotThree.Complete
