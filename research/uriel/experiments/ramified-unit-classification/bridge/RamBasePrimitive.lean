import RamBaseFive
namespace RamBase.Five

private def embed (i : Fin 16) : Fin 32 :=
  ⟨i.val/4*8 + i.val%4, by have := i.isLt; omega⟩
private def shrink (i : Fin 32) : Fin 16 :=
  ⟨i.val/8*4 + i.val%4, by have := i.isLt; omega⟩
def divisible (i : Fin 32) : Prop := (input 1 i.val).1.val % 2 = 0

private theorem embed_facts : ∀ i : Fin 16,
    shrink (embed i)=i ∧ divisible (embed i) ∧ input 1 (embed i) = input 2 i := by
  unfold divisible
  decide +kernel

private theorem shrink_facts : ∀ i : Fin 32, divisible i → embed (shrink i)=i := by
  unfold divisible
  decide +kernel

abbrev Fiber (d : ℕ) (z : D) := {x : Fin d → Fin (domain 1) // Q 1 x = z}
def allDiv {d : ℕ} {z : D} (x : Fiber d z) : Prop := ∀ i, divisible (x.1 i)

/-- The half-size input alphabet identifies exactly the all-divisible vectors
inside the unrestricted square fiber, including their original coordinate labels. -/
def divEquiv (d : ℕ) (z : D) :
    {x : Fin d → Fin (domain 2) // Q 2 x = z} ≃ {x : Fiber d z // allDiv x} where
  toFun x := ⟨⟨fun i => embed (x.1 i),by
    change (∑ i, square (input 1 (embed (x.1 i)))) = z
    calc
      _ = ∑ i, square (input 2 (x.1 i)) := Finset.sum_congr rfl
        (fun i _ => congrArg square (embed_facts (x.1 i)).2.2)
      _ = z := x.2⟩,
    fun i => (embed_facts (x.1 i)).2.1⟩
  invFun x := ⟨fun i => shrink (x.1.1 i),by
    change (∑ i, square (input 2 (shrink (x.1.1 i)))) = z
    have he (i : Fin d) : input 2 (shrink (x.1.1 i)) = input 1 (x.1.1 i) := by
      rw [← (embed_facts (shrink (x.1.1 i))).2.2,shrink_facts _ (x.2 i)]
    calc
      _ = ∑ i, square (input 1 (x.1.1 i)) := Finset.sum_congr rfl
        (fun i _ => congrArg square (he i))
      _ = z := x.1.2⟩
  left_inv x := Subtype.ext (funext fun i => (embed_facts _).1)
  right_inv x := Subtype.ext (Subtype.ext (funext fun i => shrink_facts _ (x.2 i)))

theorem primitive_card : Nat.card {x : Fiber 6 (4,0) // ¬ allDiv x} = 62914560 := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (allDiv (d:=6) (z:=(4,0))))
  rw [Nat.card_sum, ← Nat.card_congr (divEquiv 6 (4,0))] at h
  change count 2 6 (4,0) + _ = count 1 6 (4,0) at h
  rw [five_digit_divisible,five_digit_total] at h
  omega

end RamBase.Five
#print axioms RamBase.Five.primitive_card
