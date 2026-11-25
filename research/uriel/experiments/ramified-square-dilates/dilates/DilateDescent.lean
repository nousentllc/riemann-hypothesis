import RamLift
import DilateDefs

/-! Division by the uniformizer in a doubled coefficient quotient.  Writing
an even vector as π times a mixed-precision vector leaves exactly one free
bit in each scalar coordinate after reduction. -/
open Finset TargetOne
noncomputable section
namespace RamDilate.Descent
abbrev B := RamLift.B
abbrev Mixed (n : ℕ) := ZMod (n*2) × ZMod n

/-- A mixed digit stores the original π coefficient and half the original
constant coefficient. -/
def liftDigit {n : ℕ} (z : Mixed n) : B (n*2) := ⟨z.1, (z.2.val : ℕ)⟩
def pack {n : ℕ} (z : Mixed n) : B (n*2) := ⟨((2*z.2.val : ℕ) : ZMod (n*2)), z.1⟩
def unpack {n : ℕ} (x : B (n*2)) : Mixed n := (x.im, ((x.re.val / 2 : ℕ) : ZMod n))
def coarse {n : ℕ} (z : Mixed n) : B n := ⟨TargetFour.reduce n 2 z.1,z.2⟩

private theorem pack_val {n : ℕ} [NeZero n] (z : Mixed n) : (pack z).re.val=2*z.2.val := by
  apply ZMod.val_natCast_of_lt
  have := z.2.val_lt
  omega

private theorem unpack_val {n : ℕ} [NeZero n] (x : B (n*2)) :
    (unpack x).2.val = x.re.val / 2 := by
  apply ZMod.val_natCast_of_lt
  have := x.re.val_lt
  omega

private theorem pack_unpack {n : ℕ} [NeZero n] (x : B (n*2)) (hx : x.re.val%2=0) :
    pack (unpack x) = x := by
  apply QuadraticAlgebra.ext
  · apply ZMod.val_injective
    rw [pack_val,unpack_val]
    omega
  · rfl

private theorem unpack_pack {n : ℕ} [NeZero n] (z : Mixed n) :
    unpack (pack z) = z := by
  apply Prod.ext
  · rfl
  · apply ZMod.val_injective
    rw [unpack_val,pack_val]
    omega

private theorem pi_mul_lift {n : ℕ} (z : Mixed n) :
    (QuadraticAlgebra.omega : B (n*2))*liftDigit z=pack z := by
  apply QuadraticAlgebra.ext <;>
    simp [pack,liftDigit,QuadraticAlgebra.omega]

private theorem reduce_lift {n : ℕ} [NeZero n] (z : Mixed n) :
    RamLift.reduce n 2 (liftDigit z)=coarse z := by
  apply QuadraticAlgebra.ext
  · rfl
  · change TargetFour.reduce n 2 ((z.2.val : ℕ) : ZMod (n*2)) = z.2
    rw [map_natCast,ZMod.natCast_zmod_val]

private theorem scalar_cancel {n : ℕ} [NeZero n] (x y : ZMod (n*2)) :
    2*x=2*y ↔ TargetFour.reduce n 2 x=TargetFour.reduce n 2 y := by
  have h := Nat.ModEq.mul_left_cancel_iff' (a := x.val) (b := y.val) (m := n) (by decide : 2≠0)
  rw [Nat.mul_comm 2 n,←ZMod.natCast_eq_natCast_iff,←ZMod.natCast_eq_natCast_iff] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] at h
  refine h.trans ?_
  have hcast (v : ZMod (n*2)) : TargetFour.reduce n 2 v=(v.val : ZMod n) := by
    rw [←ZMod.natCast_zmod_val v, map_natCast, ZMod.natCast_zmod_val]
  rw [hcast x,hcast y]

private theorem double_cancel {n : ℕ} [NeZero n] (x y : B (n*2)) :
    2*x=2*y ↔ RamLift.reduce n 2 x=RamLift.reduce n 2 y := by
  have coord (z : B (n*2)) : (2*z).re=2*z.re ∧ (2*z).im=2*z.im := by
    simp only [two_mul,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,and_self]
  constructor
  · intro h
    apply QuadraticAlgebra.ext
    · apply (scalar_cancel x.re y.re).mp
      rw [←(coord x).1,h,(coord y).1]
    · apply (scalar_cancel x.im y.im).mp
      rw [←(coord x).2,h,(coord y).2]
  · intro h
    apply QuadraticAlgebra.ext
    · rw [(coord x).1,(coord y).1]
      exact (scalar_cancel x.re y.re).mpr (congrArg QuadraticAlgebra.re h)
    · rw [(coord x).2,(coord y).2]
      exact (scalar_cancel x.im y.im).mpr (congrArg QuadraticAlgebra.im h)

private theorem equation {n : ℕ} [NeZero n] (y : Fin 6 → Mixed n) (b : B (n*2)) :
    sqSum (fun i => pack (y i))=2*b ↔ sqSum (fun i => coarse (y i))=RamLift.reduce n 2 b := by
  have hp : (QuadraticAlgebra.omega : B (n*2))^2=2 := by
    rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
  have hL : sqSum (fun i => pack (y i))=2*sqSum (fun i => liftDigit (y i)) := by
    simp only [←pi_mul_lift,sqSum,mul_pow,hp,Finset.mul_sum]
  rw [hL,double_cancel]
  simp only [sqSum,map_sum,map_pow,reduce_lift]

private def halve {n : ℕ} [NeZero n] (b : B (n*2)) :
    {x : Fin 6 → B (n*2) // sqSum x=2*b ∧ ∀ i,(x i).re.val%2=0} ≃
    {y : Fin 6 → Mixed n // sqSum (fun i => coarse (y i))=RamLift.reduce n 2 b} where
  toFun x := ⟨fun i => unpack (x.1 i),by
    apply (equation _ _).mp
    simpa only [fun i => pack_unpack (x.1 i) (x.2.2 i)] using x.2.1⟩
  invFun y := ⟨fun i => pack (y.1 i),(equation _ _).mpr y.2,fun i => by rw [pack_val]; omega⟩
  left_inv x := Subtype.ext (funext fun i => pack_unpack (x.1 i) (x.2.2 i))
  right_inv y := Subtype.ext (funext fun i => unpack_pack (y.1 i))

private def coarseFiber {n : ℕ} (b : B n) :
    {z : Mixed n // coarse z=b} ≃ {a : ZMod (n*2) // TargetFour.reduce n 2 a=b.re} where
  toFun z := ⟨z.1.1,congrArg QuadraticAlgebra.re z.2⟩
  invFun a := ⟨(a.1,b.im),QuadraticAlgebra.ext a.2 rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl (congrArg QuadraticAlgebra.im z.2).symm)
  right_inv _ := rfl

/-- All-π-divisible solutions at a doubled target correspond to solutions
downstairs with one binary choice in each of their six coordinates. -/
theorem double_count {n : ℕ} [NeZero n] (b : B (n*2)) :
    Nat.card {x : Fin 6 → B (n*2) // sqSum x=2*b ∧ ∀ i,(x i).re.val%2=0} =
    64*count 6 (RamLift.reduce n 2 b) := by
  classical
  let _ : Fintype (B n) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let small := univ.filter fun z : Fin 6 → B n => sqSum z=RamLift.reduce n 2 b
  let g (y : Fin 6 → Mixed n) (i : Fin 6) := coarse (y i)
  have h := TargetFour.partitions g small
  have he : Nat.card {y : Fin 6 → Mixed n // sqSum (g y)=RamLift.reduce n 2 b} =
      Nat.card {y : Fin 6 → Mixed n // g y ∈ small} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x; change sqSum (g x)=_ ↔ g x ∈ Finset.filter _ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have lift (z : Fin 6 → B n) : Nat.card {x // g x=z}=64 := by
    let e : {x // g x=z} ≃ ((i : Fin 6) → {a : Mixed n // coarse a=z i}) :=
      {toFun := fun x i => ⟨x.1 i,congrFun x.2 i⟩
       invFun := fun x => ⟨fun i => (x i).1,funext fun i => (x i).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
    rw [Nat.card_congr e,Nat.card_pi]
    simp_rw [fun a => Nat.card_congr (coarseFiber a), TargetFour.scalar_count]
    decide
  have hs : small.card = count 6 (RamLift.reduce n 2 b) := by
    simp [small,count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [Nat.card_congr (halve b),he,h]
  simp only [lift,Finset.sum_const,nsmul_eq_mul,hs,Nat.mul_comm,Nat.cast_id]
end RamDilate.Descent

namespace RamDilate
/-- The imprimitive summand at the next rational digit precision. -/
theorem imprim_double_nat (r a : ℕ) :
    imprim (r+1) ((2 : S (r+1))*(a : S (r+1))) = 64*TargetOne.count 6 (a : S r) := by
  unfold imprim allEven S RamField.R
  have h := Descent.double_count (n := 2^r) (a : Descent.B ((2^r)*2))
  rw [map_natCast] at h
  exact h
end RamDilate
#print axioms RamDilate.imprim_double_nat
