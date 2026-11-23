import Formalism.SubspaceCounting.StatementB

open Finset Formalism.G0
open scoped BigOperators
namespace OrbitIncidence

private def reflect (n t d : ℕ) : ℕ := if d ≤ t then t-d else n+t-d

private theorem reflect_lt {n t d : ℕ} (ht : t<n) (hd : d<n) : reflect n t d < n := by
  unfold reflect
  split <;> omega

private theorem reflect_twice {n t d : ℕ} (ht : t<n) (hd : d<n) :
    reflect n t (reflect n t d) = d := by
  unfold reflect
  split_ifs <;> omega

private theorem sum_mod_iff {n i d t : ℕ} (hi : i<n) (hd : d<n) (ht : t<n) :
    (i+d)%n = t ↔ i = reflect n t d := by
  by_cases hlt : i+d < n
  · rw [Nat.mod_eq_of_lt hlt]
    unfold reflect
    split <;> omega
  · have hge : n ≤ i+d := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (show i+d-n < n by omega)]
    unfold reflect
    split <;> omega

/-- Exactly min(L,n) distinct cyclic starts contain any given position. -/
theorem containing_starts {n t : ℕ} (ht : t<n) (L : ℕ) :
    ((range n).filter fun i => t ∈ window n i L).card = min L n := by
  have hn : 0 < n := by omega
  have heq : ((range n).filter fun i => t ∈ window n i L) =
      (range (min L n)).image (reflect n t) := by
    ext i
    constructor
    · intro h
      obtain ⟨hi, hti⟩ := mem_filter.mp h
      obtain ⟨j, hj, hjt⟩ := mem_image.mp hti
      have hjn := Nat.mod_lt j hn
      have hindex : j%n < min L n := lt_min (lt_of_le_of_lt (Nat.mod_le j n) (mem_range.mp hj)) hjn
      refine mem_image.mpr ⟨j%n, mem_range.mpr hindex, ?_⟩
      apply ((sum_mod_iff (mem_range.mp hi) hjn ht).mp ?_).symm
      rwa [Nat.add_mod_mod]
    · intro h
      obtain ⟨j, hj, rfl⟩ := mem_image.mp h
      have hjn := (lt_min_iff.mp (mem_range.mp hj)).2
      have hir := reflect_lt ht hjn
      refine mem_filter.mpr ⟨mem_range.mpr hir, mem_image.mpr ⟨j, ?_, ?_⟩⟩
      · exact mem_range.mpr (lt_min_iff.mp (mem_range.mp hj)).1
      · exact (sum_mod_iff hir hjn ht).mpr rfl
  rw [heq, card_image_of_injOn, card_range]
  intro a ha b hb hab
  have ah := reflect_twice ht ((lt_min_iff.mp (mem_range.mp ha)).2)
  have bh := reflect_twice ht ((lt_min_iff.mp (mem_range.mp hb)).2)
  rw [hab] at ah
  exact ah.symm.trans bh

/-- Incidence identity for the source's set-valued circular window. -/
theorem total_window_occupancy (n L : ℕ) (T : Finset ℕ) (hT : T ⊆ range n) :
    ∑ i ∈ range n, (T ∩ window n i L).card = T.card * min L n := by
  let r := fun (i t : ℕ) => t ∈ window n i L
  have heq (i : ℕ) : T ∩ window n i L = T.bipartiteAbove r i := by
    ext t
    exact Finset.mem_inter.trans (Finset.mem_bipartiteAbove r).symm
  simp_rw [heq]
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  calc
    _ = ∑ _t ∈ T, min L n := by
      apply Finset.sum_congr rfl
      intro t ht
      exact containing_starts (mem_range.mp (hT ht)) L
    _ = _ := by simp

theorem cap_necessary (n L K : ℕ) (T : Finset ℕ) (hT : T ⊆ range n)
    (h : CondA n T L K) : T.card * min L n ≤ n*K := by
  rw [← total_window_occupancy n L T hT]
  calc
    _ ≤ ∑ _i ∈ range n, K := Finset.sum_le_sum fun i hi => h i (mem_range.mp hi)
    _ = _ := by simp

#print axioms containing_starts
#print axioms total_window_occupancy
#print axioms cap_necessary
end OrbitIncidence
