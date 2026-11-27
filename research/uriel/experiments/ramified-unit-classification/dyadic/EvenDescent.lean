import FourEven
open Finset TargetOne TargetFour
noncomputable section
namespace DyadicWave
def ev {m : ℕ} (d : ℕ) (b : ZMod m) :=
  Nat.card {x : Fin d → ZMod m // sqSum x=b ∧ ∀ i,(x i).val%2=0}
theorem ev_zero {m : ℕ} [NeZero m] (b : ZMod m) :
    ev 0 b = count 0 b := by
  apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
  simp
theorem ev_succ {m : ℕ} [NeZero m] (d : ℕ) (b : ZMod m) :
    ev (d+1) b = ∑ a : ZMod m, if a.val%2=0 then ev d (b-a^2) else 0 := by
  classical
  let f := fun x : {x : Fin (d+1) → ZMod m // sqSum x=b ∧ ∀ i,(x i).val%2=0} => x.1 0
  have h := partitions f univ
  simp only [Finset.mem_univ,Nat.card_subtype_true] at h
  change ev (d+1) b = _ at h
  rw [h]
  apply Finset.sum_congr rfl; intro a _
  by_cases ha : a.val%2=0
  · rw [if_pos ha]
    let e : {z // f z=a} ≃ {x : Fin d → ZMod m // sqSum x=b-a^2 ∧ ∀ i,(x i).val%2=0} :=
      {toFun := fun z => ⟨fun i => z.1.1 i.succ, by
         have q := z.1.2.1
         rw [sqSum,Fin.sum_univ_succ] at q
         have hz : z.1.1 0=a := z.2
         rw [hz] at q; dsimp [sqSum]; linear_combination q,
         fun i => z.1.2.2 i.succ⟩
       invFun := fun z => ⟨⟨Fin.cons a z.1,by
         rw [sqSum,Fin.sum_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ]
         have := z.2.1; dsimp [sqSum] at this; linear_combination this,
         Fin.cases ha (fun i => z.2.2 i)⟩,rfl⟩
       left_inv := fun z => by
         apply Subtype.ext; apply Subtype.ext
         change Fin.cons a (Fin.tail z.1.1)=z.1.1
         exact (congrArg (fun w => Fin.cons w (Fin.tail z.1.1)) z.2.symm).trans (Fin.cons_self_tail _)
       right_inv := fun z => rfl}
    exact Nat.card_congr e
  · rw [if_neg ha]
    have : IsEmpty {z // f z=a} := ⟨fun z => ha (z.2 ▸ z.1.2.2 0)⟩
    simp
private theorem equation (m t : ℕ) [NeZero m] (y : Fin 6 → ZMod (m*2)) :
    sqSum (fun i => twice m (y i))=(4*t:ℕ) ↔ sqSum (fun i => reduce m 2 (y i))=(t:ℕ) := by
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
  have h := Nat.ModEq.mul_left_cancel_iff' (a := S) (b := t) (m := m) (by decide : 4≠0)
  rw [← ZMod.natCast_eq_natCast_iff,← ZMod.natCast_eq_natCast_iff] at h
  simpa only [mul_one,Nat.cast_ofNat,Nat.cast_one] using h

private def halveSolutions (m t : ℕ) [NeZero m] :
    {x : Fin 6 → ZMod (4*m) // sqSum x=(4*t:ℕ) ∧ ∀ j, (x j).val%2=0} ≃
    {y : Fin 6 → ZMod (m*2) // sqSum (fun i => reduce m 2 (y i))=(t:ℕ)} where
  toFun x := ⟨fun i => half m (x.1 i), by
    apply (equation m t _).mp
    have h (i) : twice m (half m (x.1 i))=x.1 i := by
      apply ZMod.val_injective; rw [twice_val,half_val]
      have := x.2.2 i; omega
    simpa only [h] using x.2.1⟩
  invFun y := ⟨fun i => twice m (y.1 i), (equation m t _).mpr y.2,
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

theorem even_scaling (m t : ℕ) [NeZero m] :
    ev 6 ((4*t:ℕ):ZMod (4*m)) = 64*count 6 (t:ZMod m) := by
  classical
  let small := univ.filter fun z : Fin 6 → ZMod m => sqSum z=(t:ℕ)
  let g := fun (y : Fin 6 → ZMod (m*2)) (i : Fin 6) => reduce m 2 (y i)
  have h := partitions g small
  have he : Nat.card {y : Fin 6 → ZMod (m*2) // sqSum (g y)=(t:ℕ)} =
      Nat.card {y : Fin 6 → ZMod (m*2) // g y ∈ small} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x; change sqSum (g x)=(t:ℕ) ↔ g x ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have lift (z : Fin 6 → ZMod m) : Nat.card {x // g x=z}=64 := by
    let e : {x // g x=z} ≃ ((i : Fin 6) → {a : ZMod (m*2) // reduce m 2 a=z i}) :=
      {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
       invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
    rw [Nat.card_congr e,Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; decide
  have hs : small.card = count 6 (t:ZMod m) := by simp [small,count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [ev,Nat.card_congr (halveSolutions m t),he,h]
  simp only [lift,Finset.sum_const,nsmul_eq_mul,hs,Nat.mul_comm,Nat.cast_id]
end DyadicWave
#print axioms DyadicWave.even_scaling
