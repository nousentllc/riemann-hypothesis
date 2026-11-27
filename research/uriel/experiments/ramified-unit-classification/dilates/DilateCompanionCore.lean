import DilatePrimitive
import DilateDescent

noncomputable section
namespace RamDilate.Companion

/-- The companion multiplier is an integral unit, with inverse π−1. -/
theorem twist_isUnit {A : Type*} [CommRing A] :
    IsUnit (1+(QuadraticAlgebra.omega : QuadraticAlgebra A 2 0)) := by
  let p := (QuadraticAlgebra.omega : QuadraticAlgebra A 2 0)
  have hp : p^2=2 := by rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
  apply isUnit_iff_exists_inv.mpr
  use p-1
  change (1+p)*(p-1)=1
  linear_combination hp

/-- Reduction modulo 2 forces the π coefficient of every square to vanish. -/
theorem twist_nonsquare : ¬∃ z : RamField.O, z^2 = 1+QuadraticAlgebra.omega := by
  rintro ⟨z,h⟩
  have h₂ : (2:ZMod (2^1))=0 := by decide
  have p : RamField.digit 1 QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_zero _ | exact map_one _
  have h' := congrArg (RamField.digit 1) h
  rw [map_pow,map_add,map_one,p] at h'
  have e := congrArg QuadraticAlgebra.im h'
  rw [pow_two,QuadraticAlgebra.im_mul] at e
  change _ = 1 at e
  have hzero (s : S 1) : s.re*s.im+s.im*s.re+ (0:ZMod (2^1))*s.im*s.im=0 := by
    linear_combination s.re*s.im*h₂
  exact (by decide : (0 : ZMod (2^1)) ≠ 1) ((hzero (RamField.digit 1 z)).symm.trans e)

def child (r j : ℕ) : S r := (2:S r)^j * (1 + QuadraticAlgebra.omega)

private theorem descent (r j : ℕ) :
    imprim (r+1) (child (r+1) (j+1)) = 64*TargetOne.count 6 (child r j) := by
  have h := Descent.double_count (n := 2^r)
    ((2 : Descent.B ((2^r)*2))^j * (1+QuadraticAlgebra.omega))
  have p : RamLift.reduce (2^r) 2 QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _
  rw [map_mul,map_pow,map_ofNat,map_add,map_one,p] at h
  have a : child (r+1) (j+1) = 2*child (r+1) j := by unfold child; ring
  rw [a]
  exact h

/-- At the first resolving coefficient precision, the two opposite children
of the same half-precision cylinder always have normalized sum four. -/
theorem pair_counts
    (base2 : TargetOne.count 6 (2^2 : S 3) + TargetOne.count 6 (child 3 2) = 4*den 3)
    (base3 : TargetOne.count 6 (2^3 : S 4) + TargetOne.count 6 (child 4 3) = 4*den 4)
    (j : ℕ) (hj : 2≤j) :
    TargetOne.count 6 (2^j : S (j+1)) + TargetOne.count 6 (child (j+1) j) = 4*den (j+1) := by
  have high (n : ℕ) :
      TargetOne.count 6 (2^(n+3) : S (n+4)) +
          TargetOne.count 6 (child (n+4) (n+3)) = 4*den (n+4) := by
    induction n with
    | zero => exact base3
    | succ n ih =>
      let r := n+4
      let j := n+3
      change TargetOne.count 6 (2^(j+1) : S (r+1)) +
        TargetOne.count 6 (child (r+1) (j+1)) = 4*den (r+1)
      change TargetOne.count 6 (2^j : S r) + TargetOne.count 6 (child r j) = 4*den r at ih
      have ep : imprim (r+1) (2^(j+1) : S (r+1)) = 64*TargetOne.count 6 (2^j : S r) := by
        have h := imprim_double_nat r (2^j)
        push_cast at h
        convert h using 2; ring
      have en := descent r j
      have pp : 8*prim (r+1) (2^(j+1)) = 15*den (r+1) := by
        rw [show (2^(j+1) : S (r+1)) = 8*2^(n+1) by dsimp [j]; ring]
        exact primitive_multiple _ (by dsimp [r]; omega) _
      have pn : 8*prim (r+1) (child (r+1) (j+1)) = 15*den (r+1) := by
        rw [show child (r+1) (j+1) = 8*(2^(n+1)*(1+QuadraticAlgebra.omega)) by
          dsimp [j,child]; ring]
        exact primitive_multiple _ (by dsimp [r]; omega) _
      rw [split (r+1) (2^(j+1)),split (r+1) (child (r+1) (j+1)),ep,en]
      rw [den_succ r] at pp pn ⊢
      omega
  by_cases h : j=2
  · subst j; exact base2
  · obtain ⟨n,e⟩ := Nat.exists_eq_add_of_le (by omega : 3≤j)
    subst j
    rw [show 3+n+1=n+4 by omega,show 3+n=n+3 by omega]
    exact high n
end RamDilate.Companion
