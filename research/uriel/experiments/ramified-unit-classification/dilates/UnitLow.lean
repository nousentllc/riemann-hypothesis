import DilateLow
import DilateDefs

/-! Resolve all small coefficient bins needed by the positive branch. -/
noncomputable section
namespace RamDilate.UnitClass
open TargetOne
set_option maxRecDepth 9000
set_option maxHeartbeats 0

private def digits {r m : ℕ} (a b : Fin m) : S r := ⟨a.val,b.val⟩

/-- At modulus four the four unit targets with even π coefficient have the same count. -/
theorem low2_one (w : S 2) : count 6 ((1:S 2)+2*w)=2097152 := by
  let : Fintype (S 2) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let a : Fin 2 := ⟨w.re.val%2,Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨w.im.val%2,Nat.mod_lt _ (by decide)⟩
  have h : ∀ x : ZMod 4, 2*x=2*((x.val % 2 : ℕ):ZMod 4) := by decide +kernel
  have he : (2:S 2)*w=2*digits a b := by
    apply QuadraticAlgebra.ext
    · change 2*w.re+2*0*w.im = 2*((w.re.val%2:ℕ):ZMod 4)+2*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.re
    · change 2*w.im+0*w.re+0*0*w.im = 2*((w.im.val%2:ℕ):ZMod 4)+0*(digits (r:=2) a b).re+0*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.im
  rw [he]
  have p := project_total (RamLift.reduce 4 8) 64 (RamLift.scalar_count 4 8) ((1:S 2)+2*digits a b)
  have e : ∀ i j : Fin 2, projectedTotal (RamLift.reduce 4 8) ((1:S 2)+2*digits i j) =
    144115188075855872 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (p.trans (e a b))

/-- All sixteen refinements with odd real coefficient and even π coefficient. -/
theorem low3_one (w : S 3) : count 6 ((1:S 3)+2*w)=2147483648 := by
  let : Fintype (S 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let a : Fin 4 := ⟨w.re.val%4,Nat.mod_lt _ (by decide)⟩
  let b : Fin 4 := ⟨w.im.val%4,Nat.mod_lt _ (by decide)⟩
  have h : ∀ x : ZMod 8, 2*x=2*((x.val%4:ℕ):ZMod 8) := by decide +kernel
  have he : (2:S 3)*w=2*digits a b := by
    apply QuadraticAlgebra.ext
    · change 2*w.re+2*0*w.im = 2*((w.re.val%4:ℕ):ZMod 8)+2*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.re
    · change 2*w.im+0*w.re+0*0*w.im = 2*((w.im.val%4:ℕ):ZMod 8)+0*(digits (r:=3) a b).re+0*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.im
  rw [he]
  have p := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) ((1:S 3)+2*digits a b)
  have e : ∀ i j : Fin 4, projectedTotal (RamLift.reduce 8 4) ((1:S 3)+2*digits i j) =
    36028797018963968 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (p.trans (e a b))

/-- The four refined one-division targets with residual unit in the positive branch. -/
theorem low3_two (w : S 3) : count 6 ((2:S 3)+4*w)=2281701376 := by
  let : Fintype (S 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let a : Fin 2 := ⟨w.re.val%2,Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨w.im.val%2,Nat.mod_lt _ (by decide)⟩
  have h : ∀ x : ZMod 8, 4*x=4*((x.val%2:ℕ):ZMod 8) := by decide +kernel
  have he : (4:S 3)*w=4*digits a b := by
    apply QuadraticAlgebra.ext
    · change 4*w.re+2*0*w.im = 4*((w.re.val%2:ℕ):ZMod 8)+2*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.re
    · change 4*w.im+0*w.re+0*0*w.im = 4*((w.im.val%2:ℕ):ZMod 8)+0*(digits (r:=3) a b).re+0*0*_
      simpa only [mul_zero,zero_mul,add_zero] using h w.im
  rw [he]
  have p := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) ((2:S 3)+4*digits a b)
  have e : ∀ i j : Fin 2, projectedTotal (RamLift.reduce 8 4) ((2:S 3)+4*digits i j) =
    38280596832649216 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (p.trans (e a b))

end RamDilate.UnitClass
#print axioms RamDilate.UnitClass.low2_one
#print axioms RamDilate.UnitClass.low3_one
#print axioms RamDilate.UnitClass.low3_two
