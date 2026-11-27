import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

open Formalism.MainNotions.G
open scoped BigOperators

namespace FrobeniusWindow
noncomputable section

def source {n : ℕ} (T : Finset (Fin n)) (y : Fin n) : Fin n :=
  posAdd y (n - dMinus T y)

theorem source_spec {n : ℕ} (T : Finset (Fin n)) (y : Fin n)
    (hd : dMinus T y ≠ 0) :
    0 < dMinus T y ∧ dMinus T y ≤ n ∧ source T y ∈ T ∧ IsTypeV (source T y) := by
  classical
  unfold source
  unfold dMinus at hd ⊢
  split_ifs at hd ⊢ with h
  · exact Nat.find_spec h
  · exact absurd rfl hd

theorem source_returns {n : ℕ} (T : Finset (Fin n)) (y : Fin n)
    (hd : dMinus T y ≠ 0) : posAdd (source T y) (dMinus T y) = y := by
  have hb := (source_spec T y hd).2.1
  apply Fin.ext
  unfold source posAdd
  simp only
  rw [Nat.mod_add_mod, show y.val + (n - dMinus T y) + dMinus T y = y.val+n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt y.2]

theorem source_odd_distance {n : ℕ} (hn : Even n) (T : Finset (Fin n)) (y : Fin n)
    (hy : ¬ IsTypeV y) (hd : dMinus T y ≠ 0) : Odd (dMinus T y) := by
  obtain ⟨h1,h2,_,h4⟩ := source_spec T y hd
  unfold source IsTypeV posAdd at h4
  unfold IsTypeV at hy
  obtain ⟨k,hk⟩ := hn
  have h2n : 2 ∣ n := ⟨k,by omega⟩
  simp only at h4
  rw [Nat.even_iff,Nat.mod_mod_of_dvd _ h2n] at h4
  rw [Nat.even_iff] at hy
  rw [Nat.odd_iff]
  omega

theorem source_reduced {n : ℕ} (hn : Even n) (T : Finset (Fin n)) (y : Fin n)
    (hy : ¬ IsTypeV y) (hd : dMinus T y ≠ 0) : dMinus T y < n := by
  have h := source_odd_distance hn T y hy hd
  have hh := (source_spec T y hd).2.1
  by_contra! hle
  have heq := le_antisymm hh hle
  exact (Nat.not_odd_iff_even.mpr hn) (heq ▸ h)

open Classical in
/-- The tau predecessor charges inject into the odd exponent slots of
the even anchors on the very same orbit. -/
theorem charge_matching {n : ℕ} (hn : Even n) (T : Finset (Fin n))
    (charge : Fin n → ℝ) (credit : Fin n → ℕ → ℝ)
    (hc0 : ∀ x e, 0 ≤ credit x e)
    (hcharge : ∀ y ∈ T, ¬ IsTypeV y → dMinus T y ≠ 0 →
      charge y ≤ credit (source T y) (dMinus T y)) :
    (∑ y ∈ T.filter (fun y => ¬ IsTypeV y),
      if dMinus T y = 0 then 0 else charge y) ≤
    ∑ u ∈ (T.filter IsTypeV) ×ˢ ((Finset.range n).filter Odd), credit u.1 u.2 := by
  classical
  let A := (T.filter (fun y => ¬ IsTypeV y)).filter (fun y => dMinus T y ≠ 0)
  let f : Fin n → Fin n × ℕ := fun y => (source T y,dMinus T y)
  have inj : Set.InjOn f ↑A := by
    intro y hy z hz h
    have hdY := (Finset.mem_filter.mp hy).2
    have hdZ := (Finset.mem_filter.mp hz).2
    calc
      y = posAdd (f y).1 (f y).2 := (source_returns T y hdY).symm
      _ = posAdd (f z).1 (f z).2 := by rw [h]
      _ = z := source_returns T z hdZ
  have sub : A.image f ⊆ (T.filter IsTypeV) ×ˢ (Finset.range n).filter Odd := by
    intro u hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨ht,hy'⟩ := Finset.mem_filter.mp hy
    have ho := (Finset.mem_filter.mp ht).2
    obtain ⟨_,_,hs,hs'⟩ := source_spec T y hy'
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hs,hs'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (source_reduced hn T y ho hy'),
        source_odd_distance hn T y ho hy'⟩⟩
  have hleft : (∑ y ∈ T.filter (fun y => ¬ IsTypeV y),
      if dMinus T y = 0 then 0 else charge y) = ∑ y ∈ A, charge y := by
    unfold A
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h0 : IsTypeV y <;> by_cases h : dMinus T y = 0 <;> simp [h0,h]
  rw [hleft]
  calc
    _ ≤ ∑ y ∈ A, credit (f y).1 (f y).2 := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨ht,h0⟩ := Finset.mem_filter.mp hy
      obtain ⟨hy',ho⟩ := Finset.mem_filter.mp ht
      exact hcharge y hy' ho h0
    _ = ∑ u ∈ A.image f, credit u.1 u.2 := by
      rw [Finset.sum_image]
      exact inj
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => hc0 a.1 a.2)

/-- The capacity change is free if cap dominates b. Removing the numerator
offset costs at most that offset divided by the original power. -/
theorem charged_min_le {a b cap shift q : ℝ} (hq : 0 < q) (hs : 0 ≤ shift)
    (hb : b ≤ cap) :
    min b (a/q) ≤ min ((a-shift)/q) cap + shift/q := by
  rw [min_comm]
  calc
    min (a/q) b ≤ min ((a-shift)/q + shift/q) (cap+shift/q) :=
      min_le_min (le_of_eq (by ring)) (hb.trans (le_add_of_nonneg_right (div_nonneg hs hq.le)))
    _ = _ := min_add_add_right _ _ _

end
end FrobeniusWindow

#print axioms FrobeniusWindow.source_odd_distance
#print axioms FrobeniusWindow.charge_matching
#print axioms FrobeniusWindow.charged_min_le
