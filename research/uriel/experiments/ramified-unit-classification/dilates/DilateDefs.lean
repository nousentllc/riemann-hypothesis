import RamField
import FourEven

noncomputable section
namespace RamDilate

abbrev S (r : ℕ) := RamField.R r

noncomputable local instance (r : ℕ) : Fintype (S r) :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm

def allEven {r : ℕ} (x : Fin 6 → S r) : Prop := ∀ i, (x i).re.val % 2 = 0

def prim (r : ℕ) (b : S r) :=
  Nat.card {x : Fin 6 → S r // TargetOne.sqSum x = b ∧ ¬ allEven x}

def imprim (r : ℕ) (b : S r) :=
  Nat.card {x : Fin 6 → S r // TargetOne.sqSum x = b ∧ allEven x}

def den (r : ℕ) : ℕ := ((2^r)^2)^5

theorem split (r : ℕ) (b : S r) :
    TargetOne.count 6 b = imprim r b + prim r b := by
  classical
  let F := {x : Fin 6 → S r // TargetOne.sqSum x = b}
  let p : F → Prop := fun x => allEven x.val
  have e (q : (Fin 6 → S r) → Prop) :
      {v : F // q v.val} ≃ {x : Fin 6 → S r // TargetOne.sqSum x = b ∧ q x} :=
    {toFun := fun v => ⟨v.val.val,v.val.property,v.property⟩
     invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  calc Nat.card F = Nat.card ({x : F // p x} ⊕ {x : F // ¬p x}) :=
        Nat.card_congr (Equiv.sumCompl p).symm
       _ = _ := by
        rw [Nat.card_sum, Nat.card_congr (e allEven), Nat.card_congr (e (fun x => ¬allEven x))]
        rfl

theorem den_succ (r : ℕ) : den (r+1) = 1024 * den r := by
  unfold den
  rw [pow_succ]
  ring
end RamDilate
