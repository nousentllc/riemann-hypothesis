import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

open Formalism.G0

namespace FrobeniusSpacing


/-- Original marked-tile rule forces every retained coordinate in the tile to be even. -/
theorem marked_members_even (T : Finset ℕ) (r u b z : ℕ) (hu : 0 < u)
    (h : Formalism.G0.Marked T r u b) (hz : z ∈ T)
    (hl : b * ((6*r+1)*u) ≤ z) (hr : z < (b+1) * ((6*r+1)*u)) : Even z := by
  let a := b * ((6*r+1)*u)
  let j := (z-a) / u
  have hz' : z - a < (6*r+1)*u := by
    rw [Nat.add_mul, one_mul] at hr
    dsimp [a]
    omega
  have hj : j < 6*r+1 := (Nat.div_lt_iff_lt_mul hu).2 hz'
  have lower : j*u ≤ z-a := Nat.div_mul_le_self _ _
  have upper : z-a < (j+1)*u := by
    exact (Nat.div_lt_iff_lt_mul hu).1 (Nat.lt_succ_self _)
  have hc : z ∈ Formalism.G0.cell r u b (j+1) := by
    simp only [Formalism.G0.cell, Nat.add_sub_cancel, Finset.mem_Ico]
    exact ⟨by dsimp [a] at lower; omega, by dsimp [a] at upper; omega⟩
  obtain ⟨ho, he⟩ := h (j+1) (Nat.succ_pos _) (by omega)
  have hm := Finset.mem_inter.mpr ⟨hz, hc⟩
  by_cases he' : Even (j+1)
  · obtain ⟨x, hx, hEven⟩ := he he'
    rw [hx, Finset.mem_singleton] at hm
    exact hm.symm ▸ hEven
  · rw [ho (Nat.not_even_iff_odd.mp he')] at hm
    exact (Finset.notMem_empty _ hm).elim

/-- A positive odd displacement between two coordinates inside the same
    marked tile is impossible before reduction modulo the orbit length. -/
theorem marked_forbids_internal_odd_pair (T : Finset ℕ) (r u b z e : ℕ) (hu : 0 < u)
    (hm : Formalism.G0.Marked T r u b)
    (hz : z ∈ T) (he : Odd e)
    (hl : b * ((6*r+1)*u) ≤ z) (hr : z + e < (b+1) * ((6*r+1)*u)) :
    z + e ∉ T := by
  intro h
  have ha := marked_members_even T r u b z hu hm hz hl (by omega)
  have hb := marked_members_even T r u b (z+e) hu hm h (by omega) hr
  have hodd : Odd (z+e) := ha.add_odd he
  exact (Nat.not_even_iff_odd.mpr hodd) hb

private def T : Finset ℕ := {2, 6, 10, 15}
private def Z : Finset ℕ := {2, 6, 10, 14}

private theorem T_short (i : Fin 16) : (T ∩ window 16 i.val 8).card ≤ 3 := by
  revert i
  decide

private theorem Z_short (i : Fin 16) : (Z ∩ window 16 i.val 8).card ≤ 3 := by
  revert i
  decide

theorem one_tile_marked_with_collision : Marked T 1 2 0 := by
  intro c hc hc'
  interval_cases c <;> norm_num [T, cell, Nat.odd_iff, Nat.even_iff]

theorem one_tile_marked_without_collision : Marked Z 1 2 0 := by
  intro c hc hc'
  interval_cases c <;> norm_num [Z, cell, Nat.odd_iff, Nat.even_iff]

theorem literal_good_with_two_partners :
    GoodOrbitIntervalTileCondition 16 T 8 3 1 2 0 16 4 ∧
    15 ∈ T ∧ (15 + 3) % 16 ∈ T ∧ (15 + 7) % 16 ∈ T := by
  refine ⟨⟨fun i hi => T_short ⟨i, hi⟩, ?_, ?_⟩, by decide⟩
  · intro s hs
    have h0 : s = 0 := by omega
    subst s
    exact ⟨0, le_rfl, one_tile_marked_with_collision⟩
  · intro i _
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by decide)

theorem same_caps_without_odd_partners :
    GoodOrbitIntervalTileCondition 16 Z 8 3 1 2 0 16 4 ∧
    (∀ i e : Fin 16, i.val ∈ Z → Odd e.val → (i.val + e.val) % 16 ∉ Z) := by
  refine ⟨⟨fun i hi => Z_short ⟨i, hi⟩, ?_, ?_⟩, by decide⟩
  · intro s hs
    have h0 : s = 0 := by omega
    subst s
    exact ⟨0, le_rfl, one_tile_marked_without_collision⟩
  · intro i _
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by decide)

end FrobeniusSpacing

#print axioms FrobeniusSpacing.marked_forbids_internal_odd_pair
#print axioms FrobeniusSpacing.literal_good_with_two_partners
#print axioms FrobeniusSpacing.same_caps_without_odd_partners
