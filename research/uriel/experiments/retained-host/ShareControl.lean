import Development.AutomorphicArithmetic.PrimitiveCosets.TopsSum
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator

noncomputable section

namespace Uriel.RetainedShares

open Formalism.HC

/-- This is a published Frame constructor. No HostRaw is assumed. -/
abbrev controlFrame : Frame := cyclicFramePow 3 1

abbrev coordinate : controlFrame.A ≃+ ZMod 8 := frameCycIso 3 (2 ^ 1)

private theorem generator_coord : coordinate controlFrame.a0 = 2 := by
  exact (frameCyclic_generator 3 (2 ^ 1)).trans (by decide)

private def evenClass (z : ZMod 8) : Prop := (4 : ℕ) • z = 0

private instance (z : ZMod 8) : Decidable (evenClass z) :=
  inferInstanceAs (Decidable ((4 : ℕ) • z = 0))

private theorem mem_base_iff (t : controlFrame.A) : t ∈ controlFrame.A0 ↔ evenClass (coordinate t) := by
  constructor
  · intro ht
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
    rw [map_zsmul, generator_coord]
    change (4 : ℕ) • (k • (2 : ZMod 8)) = 0
    rw [smul_comm, show (4 : ℕ) • (2 : ZMod 8) = 0 by decide, smul_zero]
  · intro ht
    have cover : ∀ z : ZMod 8, evenClass z → ∃ k : Fin 4, k.val • (2 : ZMod 8) = z := by decide
    obtain ⟨k, hk⟩ := cover _ ht
    have hEq : k.val • controlFrame.a0 = t :=
      coordinate.injective (by rw [map_nsmul, generator_coord]; exact hk)
    rw [← hEq]
    exact controlFrame.A0.nsmul_mem (AddSubgroup.mem_zmultiples _) _

def retainedExcept (i : ZMod 8) : Finset controlFrame.A :=
  (Finset.univ.erase i).map coordinate.symm.toEquiv.toEmbedding

theorem omit_card (i : ZMod 8) : (retainedExcept i).card = 7 := by
  simp only [retainedExcept, Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, ZMod.card]

open Classical in
private theorem coset_count (i : ZMod 8) (γ : controlFrame.A) :
    ((retainedExcept i).filter (fun t => t - γ ∈ controlFrame.A0)).card =
    if (evenClass i ↔ evenClass (coordinate γ)) then 3 else 4 := by
  classical
  rw [retainedExcept, Finset.filter_map, Finset.card_map]
  have hpred : ∀ z : ZMod 8,
      coordinate.symm z - γ ∈ controlFrame.A0 ↔ evenClass (z - coordinate γ) := by
    intro z
    rw [mem_base_iff, map_sub, AddEquiv.apply_symm_apply]
  have hfilter : (Finset.univ.erase i).filter ((fun t => t - γ ∈ controlFrame.A0) ∘ coordinate.symm.toEquiv.toEmbedding) =
      (Finset.univ.erase i).filter (fun t => evenClass (t - coordinate γ)) :=
    Finset.filter_congr fun z _ => hpred z
  rw [hfilter]
  have counts : ∀ i z : ZMod 8,
      ((Finset.univ.erase i).filter (fun t => evenClass (t-z))).card =
        if (evenClass i ↔ evenClass z) then 3 else 4 := by decide
  exact counts i (coordinate γ)

open Classical in
private theorem abs_error (i : ZMod 8) (γ : controlFrame.A) :
    |(((retainedExcept i).filter (fun t => t - γ ∈ controlFrame.A0)).card : ℝ) -
      controlFrame.lam γ * ((retainedExcept i).card : ℝ)| = if evenClass i then 1 else 0 := by
  classical
  have hi : controlFrame.o = 2 := cyclicFramePow_index 3 1 (by decide)
  rw [coset_count, omit_card, Frame.lam, hi, mem_base_iff]
  by_cases h1 : evenClass i <;> by_cases h2 : evenClass (coordinate γ) <;> norm_num [h1, h2]

/-- Complete classification, including negative tolerances and the equality boundary. -/
theorem shares_iff (i : ZMod 8) (δ : ℝ) :
    controlFrame.Shares (retainedExcept i) δ ↔ (if evenClass i then (1:ℝ)/7 else 0) ≤ δ := by
  unfold Frame.Shares
  simp_rw [abs_error, omit_card]
  constructor
  · intro h
    have h0 := h 0
    by_cases hi : evenClass i <;> simp [hi] at * <;> linarith
  · intro h γ
    by_cases hi : evenClass i <;> simp [hi] at * <;> linarith

theorem matched_controls :
    controlFrame.Shares (retainedExcept 7) 0 ∧ controlFrame.Shares (retainedExcept 5) 0 ∧
    ¬ controlFrame.Shares (retainedExcept 6) (1/8) ∧ controlFrame.Shares (retainedExcept 6) (1/7) := by
  have h5 : ¬ evenClass 5 := by decide
  have h7 : ¬ evenClass 7 := by decide
  have h6 : evenClass 6 := by decide
  norm_num [shares_iff, h5, h6, h7]

/-- The sign on the two cosets is a multiplicative character of the additive group. -/
def paritySign (z : ZMod 8) : ℤ := if evenClass z then 1 else -1

theorem paritySign_character : ∀ a b : ZMod 8, paritySign (a + b) = paritySign a * paritySign b := by decide

theorem character_swap :
    (∑ t ∈ retainedExcept 7, paritySign (coordinate t)) = 1 ∧
    (∑ t ∈ retainedExcept 6, paritySign (coordinate t)) = -1 := by
  simp only [retainedExcept, Finset.sum_map, Equiv.toEmbedding_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, AddEquiv.apply_symm_apply]
  decide

/-- Extend the sign trivially across the source's auxiliary E0 factor. -/
def quotientCharacter : AddChar (Formalism.D5.E0 × controlFrame.A) ℂ where
  toFun p := (paritySign (coordinate p.2) : ℂ)
  map_zero_eq_one' := by
    change (paritySign (coordinate 0) : ℂ) = 1
    rw [map_zero, show paritySign 0 = 1 by decide]
    norm_num
  map_add_eq_mul' a b := by
    change (paritySign (coordinate (a.2 + b.2)) : ℂ) = _ * _
    rw [map_add, paritySign_character, Int.cast_mul]

theorem quotient_character_conditions :
    quotientCharacter ∈ Deduction.CH.PsiA controlFrame.A0 ∧
      ¬ ∀ t : controlFrame.A, quotientCharacter (0, t) = 1 := by
  classical
  constructor
  · simp only [Deduction.CH.PsiA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro t ht
    change (paritySign (coordinate t) : ℂ) = 1
    simp [paritySign, (mem_base_iff t).mp ht]
  · intro h
    have h1 := h (coordinate.symm 1)
    change (paritySign (coordinate (coordinate.symm 1)) : ℂ) = 1 at h1
    rw [AddEquiv.apply_symm_apply, show paritySign 1 = -1 by decide] at h1
    norm_num at h1

private theorem complex_sum (T : Finset controlFrame.A) :
    ∑ t ∈ T, quotientCharacter (0,t) = ((∑ t ∈ T, paritySign (coordinate t) : ℤ) : ℂ) := by
  push_cast
  rfl

/-- The right-hand side and main term are taken verbatim from tops_sum. -/
def characterBound (i : ZMod 8) (δ : ℝ) : Prop :=
  ‖(∑ t ∈ retainedExcept i, quotientCharacter (0, t)) -
    (((3 * (controlFrame.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ((retainedExcept i).card : ℂ)‖ ≤
    controlFrame.o * δ * ((retainedExcept i).card : ℝ)

theorem character_bound_good : characterBound 7 0 :=
  UpperTheory.Comparison₂.tops_sum _ _ _ matched_controls.1 _ quotient_character_conditions.1
    quotient_character_conditions.2

theorem character_bound_swapped (δ : ℝ) : characterBound 6 δ ↔ 1/7 ≤ δ := by
  have hi : controlFrame.o = 2 := cyclicFramePow_index 3 1 (by decide)
  unfold characterBound
  rw [complex_sum, character_swap.2, hi, omit_card]
  norm_num
  constructor <;> intro h <;> linarith

theorem shares_of_index_one (φ : Frame) (ho : φ.o = 1) (TT : Finset φ.A) {δ : ℝ} (hδ : 0 ≤ δ) :
    φ.Shares TT δ := by
  classical
  have htop : φ.A0 = ⊤ := AddSubgroup.index_eq_one.mp (φ.index_A0_eq_o.trans ho)
  intro γ
  have hn : 0 ≤ δ * (TT.card : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  norm_num [Frame.lam, htop, ho]
  exact hn

theorem principal_cyclic_level_index : (Level.cyc PChar.one).o = 1 := by
  change Nat.card (Subgroup.zpowers (1 : DirichletCharacter ℂ 1)) = 1
  simp

theorem principal_cyclic_shares {φ : Frame} (h : φ.o = (Level.cyc PChar.one).o)
    (TT : Finset φ.A) {δ : ℝ} (hδ : 0 ≤ δ) : φ.Shares TT δ :=
  shares_of_index_one φ (h.trans principal_cyclic_level_index) TT hδ

#print axioms shares_iff
#print axioms matched_controls
#print axioms paritySign_character
#print axioms character_swap
#print axioms character_bound_good
#print axioms character_bound_swapped
#print axioms principal_cyclic_shares

end Uriel.RetainedShares
