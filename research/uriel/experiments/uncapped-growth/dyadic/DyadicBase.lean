import FourBase
open TargetOne Finset
namespace DyadicWave
private def hist {m : ℕ} [NeZero m] : ℕ → ZMod m → ℕ
  | 0,b => if b=0 then 1 else 0
  | d+1,b => ∑ a : ZMod m, hist d (b-a^2)
private theorem exact_hist {m : ℕ} [NeZero m] (d : ℕ) (b : ZMod m) : count d b = hist d b := by
  induction d generalizing b with
  | zero => exact count_zero b
  | succ d ih => simp only [count_succ,hist,ih]
private theorem row_8_0 (b : ZMod 8) : hist 0 b = (![1,0,0,0,0,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_8_1 (b : ZMod 8) : hist 1 b = (![2,4,0,0,2,0,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 0 (b-a^2)) = _
  simp only [row_8_0]
  fin_cases b <;> decide
private theorem row_8_2 (b : ZMod 8) : hist 2 b = (![8,16,16,0,8,16,0,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 1 (b-a^2)) = _
  simp only [row_8_1]
  fin_cases b <;> decide
private theorem row_8_3 (b : ZMod 8) : hist 3 b = (![32,96,96,64,32,96,96,0] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 2 (b-a^2)) = _
  simp only [row_8_2]
  fin_cases b <;> decide
private theorem row_8_4 (b : ZMod 8) : hist 4 b = (![128,512,768,512,384,512,768,512] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 3 (b-a^2)) = _
  simp only [row_8_3]
  fin_cases b <;> decide
private theorem row_8_5 (b : ZMod 8) : hist 5 b = (![3072,2560,5120,5120,3072,3584,5120,5120] : Fin 8 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 8, hist 4 (b-a^2)) = _
  simp only [row_8_4]
  fin_cases b <;> decide
theorem base_eight_zero : count 6 (0 : ZMod 8) = 32768 := by
  rw [exact_hist]
  change (∑ a : ZMod 8, hist 5 (0-a^2)) = _
  simp only [row_8_5]
  decide
end DyadicWave
