import DilatePrimitiveRing
import DilatePrimitiveContact

/-! The primitive contribution for every target divisible by eight. Reduction
to modulus 32 counts all lifts of a coarse primitive vector, while the pivot
permutation splits their targets into equal-sized fibers. -/
noncomputable section
open Finset TargetOne RamLift
namespace RamDilate
namespace PrimitiveRing

private local instance (n : ℕ) [NeZero n] : Fintype (B n) :=
  Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
private local instance (n : ℕ) [NeZero n] : Fintype (V n) := Fintype.ofFinite _

private theorem red_val (k : ℕ) (z : ZMod (32*2^k)) :
    (TargetFour.reduce 32 (2^k) z).val=z.val%32 := by
  conv_lhs => rw [←ZMod.natCast_zmod_val z,map_natCast,ZMod.val_natCast]
private theorem red_odd (k : ℕ) (z : B (32*2^k)) :
    odd (reduce 32 (2^k) z) ↔ odd z := by
  change (TargetFour.reduce 32 (2^k) z.re).val%2≠0 ↔ _
  rw [red_val,Nat.mod_mod_of_dvd _ (by decide : 2∣32)]
  rfl
private theorem kernel_multiple (k : ℕ) (z : B (32*2^k)) (h : reduce 32 (2^k) z=0) :
    ∃ w, z=8*w := by
  have hr : z.re.val%32=0 := by
    rw [←red_val]; exact congrArg ZMod.val (congrArg QuadraticAlgebra.re h)
  have hi : z.im.val%32=0 := by
    rw [←red_val]; exact congrArg ZMod.val (congrArg QuadraticAlgebra.im h)
  refine ⟨⟨(z.re.val/8 : ℕ), (z.im.val/8 : ℕ)⟩, ?_⟩
  have er : z.re.val=8*(z.re.val/8) := by omega
  have ei : z.im.val=8*(z.im.val/8) := by omega
  apply QuadraticAlgebra.ext
  · change z.re=8*↑(z.re.val/8)+2*0*↑(z.im.val/8)
    simpa using congrArg (fun t : ℕ => (t:ZMod (32*2^k))) er
  · change z.im=8*↑(z.im.val/8)+0*↑(z.re.val/8)+0*0*↑(z.im.val/8)
    simpa using congrArg (fun t : ℕ => (t:ZMod (32*2^k))) ei

private def redVec (k : ℕ) (x : V (32*2^k)) : V 32 :=
  ⟨fun i => reduce 32 (2^k) (x.1 i), by obtain ⟨i,hi⟩ := x.2; exact ⟨i,(red_odd k _).2 hi⟩⟩

private def independent (k : ℕ) (y : V 32) :
    {x : V (32*2^k) // redVec k x=y} ≃
      ((i : Fin 6) → {z : B (32*2^k) // reduce 32 (2^k) z=y.1 i}) where
  toFun x i := ⟨x.1.1 i,congrFun (congrArg Subtype.val x.2) i⟩
  invFun x := ⟨⟨fun i => (x i).1,by
        obtain ⟨j,hj⟩ := y.2
        exact ⟨j,(red_odd k _).1 (by rwa [(x j).2])⟩⟩,Subtype.ext (funext fun i => (x i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lift (k : ℕ) (b : B (32*2^k)) :
    C (32*2^k) (8*b) = C 32 0*((2^k)^2)^5 := by
  classical
  let small := univ.filter fun y : V 32 => sqSum y.1=0
  let targets := univ.filter fun t : B (32*2^k) => reduce 32 (2^k) t=0
  have hs : small.card=C 32 0 := by simp [C,small,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have ht : targets.card=(2^k)^2 := by
    change (univ.filter (fun t : B (32*2^k) => reduce 32 (2^k) t=0)).card = _
    convert scalar_count 32 (2^k) 0 using 1
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have fine : ∀ t ∈ targets, C (32*2^k) t = C (32*2^k) (8*b) := by
    intro t ht
    obtain ⟨w,hw⟩ := kernel_multiple k t (Finset.mem_filter.mp ht).2
    rw [hw]
    simpa only [zero_add] using (constant k 0 w).symm.trans (constant k 0 b)
  let f := fun x : V (32*2^k) => sqSum x.1
  have h1 := TargetFour.partitions (redVec k) small
  have h2 := TargetFour.partitions f targets
  have hc (x : V (32*2^k)) : redVec k x ∈ small ↔ f x ∈ targets := by
    change _ ∈ Finset.filter _ _ ↔ _ ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change (∑ i, (reduce 32 (2^k) (x.1 i))^2)=0 ↔ reduce 32 (2^k) (∑ i,(x.1 i)^2)=0
    rw [map_sum]; simp only [map_pow]
  have he : Nat.card {x // redVec k x ∈ small}=Nat.card {x // f x ∈ targets} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun x => hc x))
  have lifts (y : V 32) : Nat.card {x // redVec k x=y}=((2^k)^2)^6 := by
    rw [Nat.card_congr (independent k y), Nat.card_pi]
    simp only [scalar_count,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [lifts] at h1
  change _ = ∑ s ∈ targets, C (32*2^k) s at h2
  rw [Finset.sum_congr rfl fine] at h2
  simp only [sum_const,nsmul_eq_mul,hs,ht] at h1 h2
  apply Nat.eq_of_mul_eq_mul_left (show 0<(2^k)^2 by positivity)
  calc _ = C 32 0*((2^k)^2)^6 := h2.symm.trans (he.symm.trans h1)
       _ = _ := by ring

theorem card_eq (r : ℕ) (b : S r) : prim r b=C (2^r) b := by
  let e : {x : Fin 6 → S r // sqSum x=b ∧ ¬allEven x} ≃ {x : V (2^r) // sqSum x.1=b} :=
    { toFun := fun x => ⟨⟨x.1,by simpa only [allEven,not_forall,odd] using x.2.2⟩,x.2.1⟩
      invFun := fun x => ⟨x.1.1,x.2,by simpa only [allEven,not_forall,odd] using x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e
end PrimitiveRing

theorem primitive_multiple (r : ℕ) (hr : 5≤r) (b : S r) :
    8*prim r (8*b)=15*den r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [PrimitiveRing.card_eq]
  have h0 : PrimitiveRing.C 32 0=15*2^47 := (PrimitiveRing.card_eq 5 0).symm.trans Contact.primitive_zero
  revert b
  unfold den S RamField.R
  rw [show 2^(5+k)=32*2^k by ring]
  intro b
  rw [PrimitiveRing.lift,h0]
  ring
end RamDilate
