import AllDepth
open Finset
namespace TargetOne
private def hist {m : ℕ} [NeZero m] : ℕ → ZMod m → ℕ
  | 0,b => if b=0 then 1 else 0
  | d+1,b => ∑ a : ZMod m, hist d (b-a^2)
private theorem agrees {m : ℕ} [NeZero m] (d : ℕ) (b : ZMod m) : count d b = hist d b := by
  induction d generalizing b with
  | zero => exact count_zero b
  | succ d ih => simp only [count_succ, hist, ih]
private theorem row_1_0 (b : ZMod 1) : hist 0 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_1_1 (b : ZMod 1) : hist 1 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 0 (b-a^2)) = _
  simp only [row_1_0]
  fin_cases b <;> decide
private theorem row_1_2 (b : ZMod 1) : hist 2 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 1 (b-a^2)) = _
  simp only [row_1_1]
  fin_cases b <;> decide
private theorem row_1_3 (b : ZMod 1) : hist 3 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 2 (b-a^2)) = _
  simp only [row_1_2]
  fin_cases b <;> decide
private theorem row_1_4 (b : ZMod 1) : hist 4 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 3 (b-a^2)) = _
  simp only [row_1_3]
  fin_cases b <;> decide
private theorem row_1_5 (b : ZMod 1) : hist 5 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 4 (b-a^2)) = _
  simp only [row_1_4]
  fin_cases b <;> decide
private theorem row_1_6 (b : ZMod 1) : hist 6 b = (![1] : Fin 1 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 1, hist 5 (b-a^2)) = _
  simp only [row_1_5]
  fin_cases b <;> decide
theorem small_1 : count 6 (1 : ZMod 1) = 1 := by
  rw [agrees,row_1_6]; decide
private theorem row_2_0 (b : ZMod 2) : hist 0 b = (![1,0] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_2_1 (b : ZMod 2) : hist 1 b = (![1,1] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 0 (b-a^2)) = _
  simp only [row_2_0]
  fin_cases b <;> decide
private theorem row_2_2 (b : ZMod 2) : hist 2 b = (![2,2] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 1 (b-a^2)) = _
  simp only [row_2_1]
  fin_cases b <;> decide
private theorem row_2_3 (b : ZMod 2) : hist 3 b = (![4,4] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 2 (b-a^2)) = _
  simp only [row_2_2]
  fin_cases b <;> decide
private theorem row_2_4 (b : ZMod 2) : hist 4 b = (![8,8] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 3 (b-a^2)) = _
  simp only [row_2_3]
  fin_cases b <;> decide
private theorem row_2_5 (b : ZMod 2) : hist 5 b = (![16,16] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 4 (b-a^2)) = _
  simp only [row_2_4]
  fin_cases b <;> decide
private theorem row_2_6 (b : ZMod 2) : hist 6 b = (![32,32] : Fin 2 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 2, hist 5 (b-a^2)) = _
  simp only [row_2_5]
  fin_cases b <;> decide
theorem small_2 : count 6 (1 : ZMod 2) = 32 := by
  rw [agrees,row_2_6]; decide
private theorem row_4_0 (b : ZMod 4) : hist 0 b = (![1,0,0,0] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_4_1 (b : ZMod 4) : hist 1 b = (![2,2,0,0] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 0 (b-a^2)) = _
  simp only [row_4_0]
  fin_cases b <;> decide
private theorem row_4_2 (b : ZMod 4) : hist 2 b = (![4,8,4,0] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 1 (b-a^2)) = _
  simp only [row_4_1]
  fin_cases b <;> decide
private theorem row_4_3 (b : ZMod 4) : hist 3 b = (![8,24,24,8] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 2 (b-a^2)) = _
  simp only [row_4_2]
  fin_cases b <;> decide
private theorem row_4_4 (b : ZMod 4) : hist 4 b = (![32,64,96,64] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 3 (b-a^2)) = _
  simp only [row_4_3]
  fin_cases b <;> decide
private theorem row_4_5 (b : ZMod 4) : hist 5 b = (![192,192,320,320] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 4 (b-a^2)) = _
  simp only [row_4_4]
  fin_cases b <;> decide
private theorem row_4_6 (b : ZMod 4) : hist 6 b = (![1024,768,1024,1280] : Fin 4 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 4, hist 5 (b-a^2)) = _
  simp only [row_4_5]
  fin_cases b <;> decide
theorem small_4 : count 6 (1 : ZMod 4) = 768 := by
  rw [agrees,row_4_6]; decide
theorem count_all (r : ℕ) : 4 * count 6 (1 : ZMod (2^r)) =
    (if r < 2 then 4 else 3) * (2^r)^5 := by
  rcases r with _ | r
  · rw [show 2^0=1 by decide,small_1]; decide
  rcases r with _ | r
  · rw [show 2^1=2 by decide,small_2]; decide
  rcases r with _ | r
  · rw [show 2^2=4 by decide,small_4]; decide
  simpa using count_one_at_depth r
end TargetOne
#print axioms TargetOne.count_all
