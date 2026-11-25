import FourLift
open Finset TargetOne
noncomputable section
namespace TargetFour
def allEven {M : ℕ} (x : Fin 6 → ZMod M) : Prop := ∀ j, (x j).val % 2=0
def evenCount (M : ℕ) := Nat.card {x : Fin 6 → ZMod M // sqSum x=4 ∧ allEven x}
def primCount (M : ℕ) := Nat.card {x : Fin 6 → ZMod M // sqSum x=4 ∧ ¬allEven x}

theorem split_count (M : ℕ) [NeZero M] :
    count 6 (4:ZMod M) = evenCount M + primCount M := by
  classical
  let F := {x : Fin 6 → ZMod M // sqSum x=4}
  let p : F → Prop := fun x => allEven x.1
  have e (q : (Fin 6 → ZMod M) → Prop) :
      {v : F // q v.1} ≃ {x : Fin 6 → ZMod M // sqSum x=4 ∧ q x} :=
    {toFun := fun v => ⟨v.1.1,v.1.2,v.2⟩
     invFun := fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  calc Nat.card F = Nat.card ({x : F // p x} ⊕ {x : F // ¬p x}) :=
        Nat.card_congr (Equiv.sumCompl p).symm
       _ = _ := by rw [Nat.card_sum, Nat.card_congr (e allEven),
                         Nat.card_congr (e (fun x => ¬allEven x))]; rfl

def twice (m : ℕ) (y : ZMod (m*2)) : ZMod (4*m) := ((2*y.val : ℕ) : ZMod (4*m))
theorem twice_val (m : ℕ) [NeZero m] (y : ZMod (m*2)) : (twice m y).val=2*y.val := by
  apply ZMod.val_natCast_of_lt
  have := y.val_lt
  omega
def half (m : ℕ) (x : ZMod (4*m)) : ZMod (m*2) := ((x.val/2 : ℕ) : ZMod (m*2))
theorem half_val (m : ℕ) [NeZero m] (x : ZMod (4*m)) : (half m x).val=x.val/2 := by
  apply ZMod.val_natCast_of_lt
  have := x.val_lt
  omega

private theorem equation (m : ℕ) [NeZero m] (y : Fin 6 → ZMod (m*2)) :
    sqSum (fun i => twice m (y i))=4 ↔ sqSum (fun i => reduce m 2 (y i))=1 := by
  let S := ∑ i, (y i).val^2
  have hL : sqSum (fun i => twice m (y i)) = ((4*S : ℕ) : ZMod (4*m)) := by
    simp only [sqSum,twice,S,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum,mul_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; norm_num
  have hR : sqSum (fun i => reduce m 2 (y i))=(S : ZMod m) := by
    simp only [sqSum,S,Nat.cast_sum,Nat.cast_pow]
    apply Finset.sum_congr rfl; intro i _
    have h := congrArg (reduce m 2) (ZMod.natCast_zmod_val (y i))
    simpa only [map_natCast] using congrArg (fun z : ZMod m => z^2) h.symm
  rw [hL,hR]
  have h := Nat.ModEq.mul_left_cancel_iff' (a := S) (b := 1) (m := m) (by decide : 4≠0)
  rw [← ZMod.natCast_eq_natCast_iff,← ZMod.natCast_eq_natCast_iff] at h
  simpa only [mul_one,Nat.cast_ofNat,Nat.cast_one] using h

def halveSolutions (m : ℕ) [NeZero m] :
    {x : Fin 6 → ZMod (4*m) // sqSum x=4 ∧ allEven x} ≃
    {y : Fin 6 → ZMod (m*2) // sqSum (fun i => reduce m 2 (y i))=1} where
  toFun x := ⟨fun i => half m (x.1 i), by
    apply (equation m _).mp
    have h (i) : twice m (half m (x.1 i))=x.1 i := by
      apply ZMod.val_injective; rw [twice_val,half_val]
      have := x.2.2 i; omega
    simpa only [h] using x.2.1⟩
  invFun y := ⟨fun i => twice m (y.1 i), (equation m _).mpr y.2,
    fun i => by rw [twice_val]; omega⟩
  left_inv x := by
    apply Subtype.ext; funext i
    apply ZMod.val_injective
    change (twice m (half m (x.1 i))).val=_
    rw [twice_val,half_val]; have := x.2.2 i; omega
  right_inv y := by
    apply Subtype.ext; funext i
    apply ZMod.val_injective
    change (half m (twice m (y.1 i))).val=_
    rw [half_val,twice_val]; omega

theorem even_scaling (m : ℕ) [NeZero m] : evenCount (4*m) = 64*count 6 (1:ZMod m) := by
  classical
  let small := univ.filter fun z : Fin 6 → ZMod m => sqSum z=1
  let g := fun (y : Fin 6 → ZMod (m*2)) (i : Fin 6) => reduce m 2 (y i)
  have h := partitions g small
  have he : Nat.card {y : Fin 6 → ZMod (m*2) // sqSum (g y)=1} =
      Nat.card {y : Fin 6 → ZMod (m*2) // g y ∈ small} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x; change sqSum (g x)=1 ↔ g x ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have lift (z : Fin 6 → ZMod m) : Nat.card {x // g x=z}=64 := by
    let e : {x // g x=z} ≃ ((i : Fin 6) → {a : ZMod (m*2) // reduce m 2 a=z i}) :=
      {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
       invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
    rw [Nat.card_congr e,Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; decide
  have hs : small.card = count 6 (1:ZMod m) := by simp [small,count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [evenCount,Nat.card_congr (halveSolutions m),he,h]
  simp only [lift,Finset.sum_const,nsmul_eq_mul,hs,Nat.mul_comm,Nat.cast_id]
end TargetFour
#print axioms TargetFour.even_scaling
