import RamBaseModel
import RamBasePivot
namespace RamBase.Five
open Finset

abbrev D := ZMod 8 × ZMod 4

/-- Every five-digit slot has a constant coefficient mod 8 and π coefficient mod 4. -/
def digit (j : ℕ) : D := ⟨(j/4 : ℕ), j⟩
def code (z : D) : ℕ := z.1.val*4 + z.2.val

theorem digit_code (z : D) : digit (code z) = z := by
  obtain ⟨a,b⟩ := z
  have hb := ZMod.val_lt b
  have h : (a.val*4+b.val)/4 = a.val := by omega
  have g : (a.val*4+b.val)%4 = b.val := by omega
  apply Prod.ext
  · simp [digit,code,h]
  · apply ZMod.val_injective
    change ((↑(a.val*4+b.val) : ZMod 4)).val = b.val
    rw [ZMod.val_natCast,g]

theorem code_lt (z : D) : code z < 32 := by
  have := ZMod.val_lt z.1
  have := ZMod.val_lt z.2
  unfold code
  omega

/-- s = 1 enumerates all 32 residues. s = 2 enumerates the 16 with even
constant coefficient. Both real and uniformizer coordinates are retained. -/
def input (s j : ℕ) : D := ⟨(s*(j/4) : ℕ), j⟩
def square (z : D) : D :=
  ⟨z.1^2 + 2 * (z.2.val : ZMod 8)^2, 2*(z.1.val : ZMod 4)*z.2⟩

def domain (s : ℕ) := 32 / s
def Q (s : ℕ) {d : ℕ} (x : Fin d → Fin (domain s)) : D :=
  ∑ i, square (input s (x i))
noncomputable def count (s d : ℕ) (b : D) := Nat.card {x : Fin d → Fin (domain s) // Q s x = b}

private def split (s d : ℕ) (b : D) :
    {x : Fin (d+1) → Fin (domain s) // Q s x = b} ≃
      Σ a : Fin (domain s), {y : Fin d → Fin (domain s) // Q s y = b-square (input s a)} where
  toFun x := ⟨x.1 0, (fun i => x.1 i.succ), by
    have h := x.2
    rw [Q, Fin.sum_univ_succ] at h
    unfold Q
    exact eq_sub_of_add_eq' h⟩
  invFun x := ⟨Fin.cons x.1 x.2.1, by
    rw [Q, Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
    have h := x.2.2
    unfold Q at h
    rw [h]; abel⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv x := by rcases x with ⟨a,y,hy⟩; rfl

theorem step (s d : ℕ) (b : D) :
    count s (d+1) b = ∑ a : Fin (domain s), count s d (b-square (input s a)) := by
  simpa only [count,Nat.card_sigma] using Nat.card_congr (split s d b)

theorem base (s : ℕ) (b : D) : count s 0 b = if b=0 then 1 else 0 := by
  classical
  by_cases h : b=0
  · subst b
    haveI : Nonempty {x : Fin 0 → Fin (domain s) // Q s x = 0} := ⟨⟨Fin.elim0,by simp [Q]⟩⟩
    simpa [count] using Nat.card_unique (α := {x : Fin 0 → Fin (domain s) // Q s x = 0})
  · haveI : IsEmpty {x : Fin 0 → Fin (domain s) // Q s x = b} := ⟨fun x => h (by simpa [Q] using x.2.symm)⟩
    simp [count,h]

def advance (s : ℕ) (f : ℕ → ℕ) (b : D) : ℕ :=
  RamBase.addUp (fun a => f (code (b - square (input s a)))) (domain s)

theorem next {s d : ℕ} {a b : ℕ → ℕ}
    (prev : ∀ z : D, count s d z = a (code z))
    (cert : RamBase.checks (fun k => decide (advance s a (digit k) = b k)) 32 = true)
    (z : D) : count s (d+1) z = b (code z) := by
  have h := of_decide_eq_true (RamBase.select cert (code z) (code_lt z))
  rw [digit_code,advance,RamBase.addUp_eq] at h
  simpa only [step,prev] using h

set_option maxHeartbeats 0
set_option maxRecDepth 12000
def h1_0 (k : ℕ) : ℕ := ((0x1 : ℕ) >>> (1*k)) % 2
theorem h1_base (z : D) : count 1 0 z = h1_0 (code z) := by
  have cert : RamBase.checks (fun k => decide ((if digit k=0 then 1 else 0 : ℕ) = h1_0 k)) 32 = true := by decide +kernel
  simpa only [base,digit_code] using of_decide_eq_true (RamBase.select cert (code z) (code_lt z))
def h1_1 (k : ℕ) : ℕ := ((0x4000000040800000400080004 : ℕ) >>> (4*k)) % 16
theorem h1_step1 (z : D) : count 1 1 z = h1_1 (code z) := by
  exact next h1_base (by decide +kernel) z
def h1_2 (k : ℕ) : ℕ := ((0x40004000000080004000400080004000400040000000800040004000000040 : ℕ) >>> (8*k)) % 256
theorem h1_step2 (z : D) : count 1 2 z = h1_2 (code z) := by
  exact next h1_step1 (by decide +kernel) z
def h1_3 (k : ℕ) : ℕ := ((0x600000c00000600000a00000c00000600000600000a00000600000800000600000a00000800000600000600000a00 : ℕ) >>> (12*k)) % 4096
theorem h1_step3 (z : D) : count 1 3 z = h1_3 (code z) := by
  exact next h1_step2 (by decide +kernel) z
def h1_4 (k : ℕ) : ℕ := ((0x400000001000000004000000010000000040000000100000000300000001200000004000000010000000040000000100000000400000001000000003000000016000 : ℕ) >>> (17*k)) % 131072
theorem h1_step4 (z : D) : count 1 4 z = h1_4 (code z) := by
  exact next h1_step3 (by decide +kernel) z
def h1_5 (k : ℕ) : ℕ := ((0x210000000001e0000000001e000000000220000000001e000000000210000000001e00000000022000000000230000000001e0000000001e000000000220000000001e000000000230000000001e000000000220000 : ℕ) >>> (22*k)) % 4194304
theorem h1_step5 (z : D) : count 1 5 z = h1_5 (code z) := by
  exact next h1_step4 (by decide +kernel) z
def h1_6 (k : ℕ) : ℕ := ((0x1000000000000040000000000000f00000000000044000000000001000000000000040000000000001040000000000040000000000001000000000000040000000000000f00000000000044000000000001000000000000040000000000000fc000000000004000000 : ℕ) >>> (27*k)) % 134217728
theorem h1_step6 (z : D) : count 1 6 z = h1_6 (code z) := by
  exact next h1_step5 (by decide +kernel) z
def h2_0 (k : ℕ) : ℕ := ((0x1 : ℕ) >>> (1*k)) % 2
theorem h2_base (z : D) : count 2 0 z = h2_0 (code z) := by
  have cert : RamBase.checks (fun k => decide ((if digit k=0 then 1 else 0 : ℕ) = h2_0 k)) 32 = true := by decide +kernel
  simpa only [base,digit_code] using of_decide_eq_true (RamBase.select cert (code z) (code_lt z))
def h2_1 (k : ℕ) : ℕ := ((0x4000004000004000004 : ℕ) >>> (3*k)) % 8
theorem h2_step1 (z : D) : count 2 1 z = h2_1 (code z) := by
  exact next h2_base (by decide +kernel) z
def h2_2 (k : ℕ) : ℕ := ((0x40000000000000400000000000004000000000000040 : ℕ) >>> (7*k)) % 128
theorem h2_step2 (z : D) : count 2 2 z = h2_2 (code z) := by
  exact next h2_step1 (by decide +kernel) z
def h2_3 (k : ℕ) : ℕ := ((0x400000000000000000000040000000000000000000004000000000000000000000400 : ℕ) >>> (11*k)) % 2048
theorem h2_step3 (z : D) : count 2 3 z = h2_3 (code z) := by
  exact next h2_step2 (by decide +kernel) z
def h2_4 (k : ℕ) : ℕ := ((0x4000000000000000000000000000004000000000000000000000000000004000000000000000000000000000004000 : ℕ) >>> (15*k)) % 32768
theorem h2_step4 (z : D) : count 2 4 z = h2_4 (code z) := by
  exact next h2_step3 (by decide +kernel) z
def h2_5 (k : ℕ) : ℕ := ((0x40000000000000000000000000000000000000400000000000000000000000000000000000004000000000000000000000000000000000000040000 : ℕ) >>> (19*k)) % 524288
theorem h2_step5 (z : D) : count 2 5 z = h2_5 (code z) := by
  exact next h2_step4 (by decide +kernel) z
def h2_6 (k : ℕ) : ℕ := ((0x400000000000000000000000000000000000000000000040000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000400000 : ℕ) >>> (23*k)) % 8388608
theorem h2_step6 (z : D) : count 2 6 z = h2_6 (code z) := by
  exact next h2_step5 (by decide +kernel) z

theorem five_digit_total : count 1 6 (4,0) = 67108864 := by rw [h1_step6]; decide +kernel
theorem five_digit_divisible : count 2 6 (4,0) = 4194304 := by rw [h2_step6]; decide +kernel
theorem five_digit_difference :
    8 * (count 1 6 (4,0) - count 2 6 (4,0)) = 15 * 32^5 := by
  rw [five_digit_total,five_digit_divisible]; decide +kernel
end RamBase.Five
#print axioms RamBase.Five.five_digit_difference
