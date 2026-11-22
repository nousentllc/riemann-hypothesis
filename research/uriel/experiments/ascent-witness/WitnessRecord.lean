import SlotApplication

open UpperTheory.V.Win

namespace AscentWitness

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem near_integer (z : ℤ) (k : ℕ) :
    ‖(z : ℚ_[3])‖ < (3 : ℝ) ^ (-(k : ℤ)) ↔ (3 : ℤ) ^ (k + 1) ∣ z := by
  have hd := Padic.norm_int_le_pow_iff_dvd (p := 3) z (k+1)
  change ‖(z : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-((k+1 : ℕ) : ℤ)) ↔ (3 : ℤ) ^ (k+1) ∣ z at hd
  rw [← hd]
  by_cases h : z = 0
  · subst z
    simp <;> positivity
  · have hz : (z : ℚ_[3]) ≠ 0 := by exact_mod_cast h
    rw [Padic.norm_eq_zpow_neg_valuation hz, show ((3 : ℕ) : ℝ) = 3 by norm_num,
      zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3),
      zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)]
    push_cast
    omega

/-- Label 0 represents the empty set. Every other label represents its positive weight. -/
theorem label_answers (Z : ℕ) (a : Fin (Z + 1)) (e : ℕ) (he : 1 ≤ e) (hle : e ≤ Z) :
    e ∈ SlotThree.weightsAt (a.val : ℚ_[3]) Z ↔ a.val = e := by
  classical
  simp only [SlotThree.weightsAt, Finset.mem_filter, Finset.mem_Icc, he, hle, and_self, true_and]
  rw [← show (((a.val : ℤ) - e : ℤ) : ℚ_[3]) = (a.val : ℚ_[3]) - e by push_cast; rfl,
      near_integer]
  constructor
  · intro h
    have hd : ((a.val : ℤ) - e).natAbs ≤ Z := by have := a.isLt; omega
    have hz := Nat.lt_pow_succ_log_self (by decide : 1 < 3) Z
    have heq := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by
      rw [Int.natAbs_pow]
      change _ < (3 : ℕ) ^ (Nat.log 3 Z + 1)
      exact lt_of_le_of_lt hd hz)
    omega
  · intro h
    simp [h]

theorem admissible_label (h : SlotThree.TowerClassHyp) (Z : ℕ) (a : Fin (Z+1)) :
    (SlotThree.SingleCenter (a.val : ℚ_[3]) ∧ SecondBound 3 1 SlotThree.L) ∧
    FirstBound 3 1 1 SlotThree.L Z (SlotThree.weightsAt (a.val : ℚ_[3]) Z) :=
  ⟨SlotThree.any_center h _, SlotThree.firstBound_of_card h _ _ (SlotThree.card_weightsAt _ _)⟩

/-- A tag read once must answer every later in-range membership query. -/
theorem enough_tags (Z : ℕ) {T : Type*} [Fintype T] (record : Fin (Z+1) → T)
    (read : T → ℕ → Prop) (faithful : ∀ a e, 1 ≤ e → e ≤ Z →
      (read (record a) e ↔ e ∈ SlotThree.weightsAt (a.val : ℚ_[3]) Z)) :
    Z + 1 ≤ Fintype.card T := by
  have hinj : Function.Injective record := by
    intro a b hab
    apply Fin.ext
    have same (e : ℕ) (h : 1 ≤ e) (hz : e ≤ Z) : a.val = e ↔ b.val = e := by
      rw [← label_answers Z a e h hz, ← label_answers Z b e h hz,
        ← faithful a e h hz, ← faithful b e h hz, hab]
    have ha := a.isLt
    have hb := b.isLt
    by_cases pos : 1 ≤ a.val
    · exact ((same a.val pos (by omega)).mp rfl).symm
    · by_cases posb : 1 ≤ b.val
      · exact (same b.val posb (by omega)).mpr rfl
      · omega
  simpa using Fintype.card_le_of_injective record hinj

/-- All p-adic centers of the cap-one filter admit the matching finite tag. -/
theorem tag_exists (Z : ℕ) (s : ℚ_[3]) :
    ∃ a : Fin (Z+1), ∀ e : ℕ, 1 ≤ e → e ≤ Z → (e ∈ SlotThree.weightsAt s Z ↔ a.val = e) := by
  classical
  by_cases empty : SlotThree.weightsAt s Z = ∅
  · exact ⟨0, fun e he _ => by simp [empty]; omega⟩
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have range := Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1
    refine ⟨⟨u, by omega⟩, fun e _ _ => ⟨fun he => ?_, fun he => he ▸ hu⟩⟩
    exact Finset.card_le_one.mp (SlotThree.card_weightsAt s Z) u hu e he

#print axioms near_integer
#print axioms label_answers
#print axioms admissible_label
#print axioms enough_tags
#print axioms tag_exists

end AscentWitness
