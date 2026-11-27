import DilateLow
import DilateDefs

/-! Four kernel-reduced coarse target bins, already sufficient for the whole companion cylinder. -/
noncomputable section
namespace RamDilate.Companion
open TargetOne

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem low2_twice : count 6 ((2 : S 2)*(1+QuadraticAlgebra.omega)) = 1966080 := by
  let : Fintype (S 2) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 4 8) 64 (RamLift.scalar_count 4 8)
      ((2 : S 2)*(1+QuadraticAlgebra.omega))
  have e : projectedTotal (RamLift.reduce 4 8)
      ((2 : S 2)*(1+QuadraticAlgebra.omega)) = 135107988821114880 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

private def digitPair (a b : Fin 2) : S 3 := ⟨a.val,b.val⟩

private theorem low3_twice_bins (a b : Fin 2) :
    count 6 ((2 : S 3)*(1+QuadraticAlgebra.omega)+4*digitPair a b) = 2013265920 := by
  let : Fintype (S 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4)
      ((2 : S 3)*(1+QuadraticAlgebra.omega)+4*digitPair a b)
  have e : ∀ i j : Fin 2, projectedTotal (RamLift.reduce 8 4)
      ((2 : S 3)*(1+QuadraticAlgebra.omega)+4*digitPair i j) =
        33776997205278720 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans (e a b))

theorem low3_twice (w : S 3) :
    count 6 ((2 : S 3)*(1+QuadraticAlgebra.omega)+4*w) = 2013265920 := by
  let a : Fin 2 := ⟨w.re.val % 2, Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨w.im.val % 2, Nat.mod_lt _ (by decide)⟩
  have e : ∀ x : ZMod 8, 4*x = 4*((x.val % 2 : ℕ) : ZMod 8) := by decide +kernel
  have he : (4:S 3)*w = 4*digitPair a b := by
    apply QuadraticAlgebra.ext
    · change 4*w.re+2*0*w.im = 4*((w.re.val % 2 : ℕ):ZMod 8)+2*0*_
      simpa only [mul_zero,zero_mul,add_zero] using e w.re
    · change 4*w.im+0*w.re+0*0*w.im =
          4*((w.im.val % 2 : ℕ):ZMod 8)+0*(digitPair a b).re+0*0*_
      simpa only [mul_zero,zero_mul,add_zero] using e w.im
  rw [he]
  exact low3_twice_bins a b

end RamDilate.Companion
#print axioms RamDilate.Companion.low2_twice
#print axioms RamDilate.Companion.low3_twice
