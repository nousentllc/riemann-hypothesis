import Shallow
open Finset TargetOne
namespace TargetFour
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
private def hist {m : ℕ} [NeZero m] : ℕ → ZMod m → ℕ
  | 0,b => if b=0 then 1 else 0
  | d+1,b => ∑ a : ZMod m, hist d (b-a^2)
private theorem exact_hist {m : ℕ} [NeZero m] (d : ℕ) (b : ZMod m) : count d b = hist d b := by
  induction d generalizing b with
  | zero => exact count_zero b
  | succ d ih => simp only [count_succ,hist,ih]
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
theorem base_1 : count 6 (4 : ZMod 1) = 1 := by
  rw [exact_hist]
  change (∑ a : ZMod 1, hist 5 (4-a^2)) = _
  simp only [row_1_5]
  decide
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
theorem base_2 : count 6 (4 : ZMod 2) = 32 := by
  rw [exact_hist]
  change (∑ a : ZMod 2, hist 5 (4-a^2)) = _
  simp only [row_2_5]
  decide
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
theorem base_4 : count 6 (4 : ZMod 4) = 1024 := by
  rw [exact_hist]
  change (∑ a : ZMod 4, hist 5 (4-a^2)) = _
  simp only [row_4_5]
  decide
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
theorem base_8 : count 6 (4 : ZMod 8) = 32768 := by
  rw [exact_hist]
  change (∑ a : ZMod 8, hist 5 (4-a^2)) = _
  simp only [row_8_5]
  decide
private theorem row_16_0 (b : ZMod 16) : hist 0 b = (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_16_1 (b : ZMod 16) : hist 1 b = (![4,4,0,0,4,0,0,0,0,4,0,0,0,0,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 0 (b-a^2)) = _
  simp only [row_16_0]
  fin_cases b <;> decide
private theorem row_16_2 (b : ZMod 16) : hist 2 b = (![16,32,32,0,32,32,0,0,16,32,32,0,0,32,0,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 1 (b-a^2)) = _
  simp only [row_16_1]
  fin_cases b <;> decide
private theorem row_16_3 (b : ZMod 16) : hist 3 b = (![64,384,384,256,192,384,384,0,192,384,384,256,64,384,384,0] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 2 (b-a^2)) = _
  simp only [row_16_2]
  fin_cases b <;> decide
private theorem row_16_4 (b : ZMod 16) : hist 4 b = (![512,4096,6144,4096,3072,4096,6144,4096,1536,4096,6144,4096,3072,4096,6144,4096] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 3 (b-a^2)) = _
  simp only [row_16_3]
  fin_cases b <;> decide
private theorem row_16_5 (b : ZMod 16) : hist 5 b = (![47104,40960,81920,81920,47104,57344,81920,81920,51200,40960,81920,81920,51200,57344,81920,81920] : Fin 16 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 16, hist 4 (b-a^2)) = _
  simp only [row_16_4]
  fin_cases b <;> decide
theorem base_16 : count 6 (4 : ZMod 16) = 1032192 := by
  rw [exact_hist]
  change (∑ a : ZMod 16, hist 5 (4-a^2)) = _
  simp only [row_16_5]
  decide
private theorem row_32_0 (b : ZMod 32) : hist 0 b = (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  fin_cases b <;> decide
private theorem row_32_1 (b : ZMod 32) : hist 1 b = (![4,4,0,0,8,0,0,0,0,4,0,0,0,0,0,0,4,4,0,0,0,0,0,0,0,4,0,0,0,0,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 0 (b-a^2)) = _
  simp only [row_32_0]
  fin_cases b <;> decide
private theorem row_32_2 (b : ZMod 32) : hist 2 b = (![32,64,64,0,64,64,0,0,64,64,64,0,0,64,0,0,32,64,64,0,64,64,0,0,0,64,64,0,0,64,0,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 1 (b-a^2)) = _
  simp only [row_32_1]
  fin_cases b <;> decide
private theorem row_32_3 (b : ZMod 32) : hist 3 b = (![256,1536,1536,1024,768,1536,1536,0,768,1536,1536,1024,512,1536,1536,0,256,1536,1536,1024,768,1536,1536,0,768,1536,1536,1024,0,1536,1536,0] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 2 (b-a^2)) = _
  simp only [row_32_2]
  fin_cases b <;> decide
private theorem row_32_4 (b : ZMod 32) : hist 4 b = (![2048,32768,49152,32768,24576,32768,49152,32768,12288,32768,49152,32768,24576,32768,49152,32768,6144,32768,49152,32768,24576,32768,49152,32768,12288,32768,49152,32768,24576,32768,49152,32768] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 3 (b-a^2)) = _
  simp only [row_32_3]
  fin_cases b <;> decide
private theorem row_32_5 (b : ZMod 32) : hist 5 b = (![753664,655360,1310720,1310720,737280,917504,1310720,1310720,819200,655360,1310720,1310720,819200,917504,1310720,1310720,753664,655360,1310720,1310720,770048,917504,1310720,1310720,819200,655360,1310720,1310720,819200,917504,1310720,1310720] : Fin 32 → ℕ) ⟨b.val,b.val_lt⟩ := by
  change (∑ a : ZMod 32, hist 4 (b-a^2)) = _
  simp only [row_32_4]
  fin_cases b <;> decide
theorem base_32 : count 6 (4 : ZMod 32) = 33030144 := by
  rw [exact_hist]
  change (∑ a : ZMod 32, hist 5 (4-a^2)) = _
  simp only [row_32_5]
  decide
end TargetFour
#print axioms TargetFour.base_32
