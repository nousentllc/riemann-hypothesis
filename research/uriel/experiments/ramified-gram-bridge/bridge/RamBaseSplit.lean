import RamBase
import RamBaseReduction
import RamBasePrimitive

namespace RamBase.Split
open Finset
noncomputable local instance : Fintype R := Fintype.ofEquiv Pair equiv.symm
abbrev π := RamBase.Five.pi32
abbrev Vec := Fin 6 → R
def divides (z : R) : Prop := z.re.val%2=0
def high (z : R) : Bool := decide (16 ≤ z.im.val)
def recover (x : R) (tag : Bool) : R :=
  ⟨x.im, ((x.re.val / 2 + (if tag then 16 else 0) : ℕ) : ZMod 32)⟩
set_option maxRecDepth 12000
set_option maxHeartbeats 0

private def parityTest (t : ℕ) : Bool :=
  let z := decode t
  decide (
    (π*z).re.val%2=0 ∧ recover (π*z) (high z)=z ∧
    (z.re.val%2=0 → ∀ b : Bool, π*recover z b = z ∧ high (recover z b)=b))
private theorem allParities : checks parityTest 1024=true := by decide +kernel
private theorem parities (z : R) :
    divides (π*z) ∧ recover (π*z) (high z)=z ∧
      (divides z → ∀ b : Bool, π*recover z b=z ∧ high (recover z b)=b) := by
  simpa only [decode_encode,divides] using
    of_decide_eq_true (select allParities (encode z) (encode_lt z))

abbrev Packed := {x : Vec // TargetOne.sqSum x = 4 ∧ ∀ i, divides (x i)}
abbrev Scaled := {y : Vec // 2*TargetOne.sqSum y = 4}
abbrev Fiber := {x : Vec // TargetOne.sqSum x = 4}
def allEven (x : Fiber) : Prop := ∀ i, divides (x.1 i)
theorem scaled (x : Vec) : TargetOne.sqSum (fun i => π*x i) = 2*TargetOne.sqSum x := by
  simp [TargetOne.sqSum,mul_pow,RamBase.Five.pi32_square,Finset.mul_sum]

/-- Inverse branches of multiplication by π in each coordinate are indexed by
the high bit of its π coefficient and preserve the quadratic equation. -/
def branches : Scaled ≃ Packed × (Fin 6 → Bool) where
  toFun y := (⟨fun i => π*y.1 i, (scaled y.1).trans y.2, fun i => (parities _).1⟩,
    fun i => high (y.1 i))
  invFun x := ⟨fun i => recover (x.1.1 i) (x.2 i),by
    rw [← scaled]
    have h (i : Fin 6) : π*recover (x.1.1 i) (x.2 i) = x.1.1 i :=
      ((parities _).2.2 (x.1.2.2 i) _).1
    simpa only [h] using x.1.2.1⟩
  left_inv y := Subtype.ext (funext fun i => (parities (y.1 i)).2.1)
  right_inv x := Prod.ext
    (Subtype.ext (funext fun i => ((parities (x.1.1 i)).2.2 (x.1.2.2 i) _).1))
    (funext fun i => ((parities (x.1.1 i)).2.2 (x.1.2.2 i) _).2)

abbrev T := {t : R // 2*t=4}

private def target (j : Fin 4) : R :=
  ⟨((2+16*(j.val/2) : ℕ) : ZMod 32), ((16*(j.val%2) : ℕ) : ZMod 32)⟩
private def targetIdx (t : R) : Fin 4 :=
  ⟨t.re.val/16*2+t.im.val/16, by have := ZMod.val_lt t.re; have := ZMod.val_lt t.im; omega⟩
private theorem tleft : ∀ j : Fin 4, 2*target j=4 ∧ targetIdx (target j)=j := by decide +kernel
private theorem tright : checks (fun k => decide
    (2*decode k=4 → target (targetIdx (decode k))=decode k)) 1024=true := by decide +kernel
private def targets : Fin 4 ≃ T where
  toFun j := ⟨target j,(tleft j).1⟩
  invFun t := targetIdx t.1
  left_inv j := (tleft j).2
  right_inv t := by
    apply Subtype.ext
    have h := of_decide_eq_true (select tright (encode t.1) (encode_lt _))
    rw [decode_encode] at h
    exact h t.2

private def separate : Scaled ≃ Σ t : T, {y : Vec // TargetOne.sqSum y=t.1} where
  toFun y := ⟨⟨_,y.2⟩,y.1,rfl⟩
  invFun x := ⟨x.2.1,by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨t,ht⟩,⟨y,hy⟩⟩
    change TargetOne.sqSum y = t at hy
    subst t
    rfl

theorem count_scaled : Nat.card Scaled = 4*(17*2^47) := by
  classical
  letI : Fintype T := Fintype.ofEquiv _ targets
  rw [Nat.card_congr separate,Nat.card_sigma,←targets.sum_comp]
  change (∑ j : Fin 4, TargetOne.count 6 (target j)) = _
  simp only [census_six]
  decide +kernel

theorem imprimitive : Nat.card Packed = 17*2^43 := by
  have h := Nat.card_congr branches
  rw [Nat.card_prod, count_scaled] at h
  have hc : Nat.card (Fin 6 → Bool)=64 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [hc] at h
  omega

private def packEquiv : Packed ≃ {x : Fiber // allEven x} where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem primitive : Nat.card {x : Fiber // ¬ allEven x} = 15*2^47 := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl allEven)
  rw [Nat.card_sum,←Nat.card_congr packEquiv,imprimitive] at h
  change _ + _ = TargetOne.count 6 (4:R) at h
  rw [count_four] at h
  omega

theorem primitive_agrees_with_five :
    Nat.card {x : Fiber // ¬ allEven x} =
      32^5 * Nat.card {x : Five.Fiber 6 (4,0) // ¬ Five.allDiv x} := by
  rw [primitive,Five.primitive_card]; decide +kernel
end RamBase.Split
#print axioms RamBase.Split.imprimitive
#print axioms RamBase.Split.primitive_agrees_with_five
