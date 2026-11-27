import CompanionPrimitive
import CompanionObstruction
import CompanionLow
import DilateLowCompanion

/-! Exact counts on the entire resolved target cylinder. -/
noncomputable section
namespace RamDilate.Companion
open TargetOne

private theorem red_omega (n m : ℕ) :
    RamLift.reduce n m QuadraticAlgebra.omega = QuadraticAlgebra.omega := by
  apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _

private theorem impossible (r : ℕ) (w : S (r+1)) :
    count 6 (1+QuadraticAlgebra.omega+2*w) = 0 := by
  revert w
  unfold S RamField.R
  rw [show 2^(r+1)=2*2^r by rw [pow_succ,Nat.mul_comm]]
  intro w
  have : IsEmpty {x : Fin 6 → RamLift.B (2*2^r) //
      sqSum x = 1+QuadraticAlgebra.omega+2*w} := ⟨fun x => by
    have h := congrArg (RamLift.reduce 2 (2^r)) x.property
    simp only [sqSum,map_sum,map_pow,map_add,map_one,red_omega,map_mul,map_ofNat] at h
    rw [show (2:RamLift.B 2)=0 by decide +kernel,zero_mul,add_zero] at h
    have hi := congrArg QuadraticAlgebra.im h
    change (sqSum (fun i => RamLift.reduce 2 (2^r) (x.val i))).im = 1 at hi
    exact (by decide : (0:ZMod 2) ≠ 1) ((sum_mod_two_im_zero _).symm.trans hi)⟩
  exact Nat.card_of_isEmpty

/-- A scalar-square multiple of the companion, perturbed inside its resolved coefficient cylinder. -/
def target (r j : ℕ) (w : S r) : S r :=
  (2:S r)^j*(1+QuadraticAlgebra.omega)+(2:S r)^(j+1)*w

private def truncate (r : ℕ) (w : S (r+1)) : S r :=
  RamLift.reduce (2^r) 2 w

private theorem target_one (r : ℕ) (w : S r) :
    target r 1 w = (2:S r)*(1+QuadraticAlgebra.omega)+4*w := by
  unfold target
  ring

private theorem target_two (r : ℕ) (w : S r) :
    target r 2 w = (4:S r)*(1+QuadraticAlgebra.omega)+8*w := by
  unfold target
  ring

private theorem down (r j : ℕ) (w : S (r+1)) :
    imprim (r+1) (target (r+1) (j+1) w) =
      64*count 6 (target r j (truncate r w)) := by
  rw [show target (r+1) (j+1) w = 2*target (r+1) j w by unfold target; ring]
  have h := Descent.double_count (n := 2^r) (target (r+1) j w)
  let f : S (r+1) →+* S r := RamLift.reduce (2^r) 2
  have hp : f QuadraticAlgebra.omega = QuadraticAlgebra.omega := red_omega (2^r) 2
  have e : f (target (r+1) j w) = target r j (truncate r w) := by
    simp only [target,map_add,map_mul,map_pow,map_ofNat,map_one,hp]
    rfl
  rw [show RamLift.reduce (2^r) 2 (target (r+1) j w) = _ from e] at h
  exact h

private theorem twice_imprim (r : ℕ) (hr : 2≤r) (w : S r) :
    imprim r (target r 1 w) = 0 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  change imprim ((n+1)+1) (target ((n+1)+1) (0+1) w) = 0
  rw [down]
  have ht (z : S (n+1)) : target (n+1) 0 z = 1+QuadraticAlgebra.omega+2*z := by
    unfold target
    ring
  rw [ht, impossible, mul_zero]

private theorem twice (r : ℕ) (hr : 2≤r) (w : S r) :
    8*count 6 (target r 1 w) = 15*den r := by
  by_cases hr3 : 3≤r
  · rw [split, twice_imprim r hr,zero_add]
    rw [target_one]
    apply CompanionPrimitive.primitive_later 2 4 r hr3
    intro b
    have h := split 3 (target 3 1 b)
    rw [twice_imprim 3 (by decide),zero_add] at h
    rw [target_one,low3_twice] at h
    change 8*prim 3 (target 3 1 b) = _
    rw [target_one,← h]
    decide +kernel
  · obtain rfl : r=2 := by omega
    rw [target_one,show (4:S 2)=0 by decide +kernel,zero_mul,add_zero,low2_twice]
    decide +kernel

private theorem primitive_four (r : ℕ) (hr : 3≤r) (w : S r) :
    8*prim r (target r 2 w) = 15*den r := by
  rw [target_two]
  apply CompanionPrimitive.primitive_later 4 8 r hr
  intro b
  change 8*prim 3 ((4:S 3)*(1+QuadraticAlgebra.omega)+8*b)=15*den 3
  rw [show (8:S 3)=0 by decide +kernel,zero_mul,add_zero]
  have h := split 3 (target 3 2 0)
  rw [down] at h
  have ht : count 6 (target 2 1 (truncate 2 (0:S 3))) = 1966080 := by
    have hz : truncate 2 (0:S 3) = 0 := map_zero _
    rw [target_one,hz,mul_zero,add_zero,low2_twice]
  rw [ht,target_two] at h
  simp only [mul_zero,add_zero] at h
  rw [low3_four_companion] at h
  change _ = 15*1073741824
  omega

private theorem primitive_eight (r : ℕ) (hr : 3≤r) (b : S r) :
    8*prim r (8*b)=15*den r := by
  have h0 := CompanionPrimitive.primitive_later 0 8 r hr (by
    intro w
    change 8*prim 3 (0*(1+QuadraticAlgebra.omega)+(8:S 3)*w)=15*den 3
    rw [show (8:S 3)=0 by decide +kernel,zero_mul,zero_mul,zero_add]
    have h := split 3 (0:S 3)
    have hi := imprim_double_nat 2 0
    simp only [Nat.cast_zero,mul_zero,low2_zero] at hi
    rw [low3_zero,hi] at h
    change _ = 15*1073741824
    omega) b
  simpa only [Nat.cast_zero,zero_mul,zero_add,Nat.cast_ofNat] using h0

/-- Exact count at every resolving coefficient depth, on the entire target cylinder. -/
theorem band (j r : ℕ) (hj : 2≤j) (hr : j+1≤r) (w : S r) :
    16^j*count 6 (target r j w) + 2*den r = 2*16^j*den r := by
  induction j generalizing r with
  | zero => omega
  | succ j ih =>
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have h := down s j w
    rw [split,h]
    by_cases hj1 : j=1
    · subst j
      have hp := primitive_four (s+1) (by omega) w
      have ht := twice s (by omega) (truncate s w)
      change 16^2*(64*count 6 (target s 1 (truncate s w))+prim (s+1) (target (s+1) 2 w)) +
        2*den (s+1) = 2*16^2*den (s+1)
      rw [den_succ s] at hp ⊢
      norm_num at *
      omega
    · have hj2 : 2≤j := by omega
      have hs3 : 3 ≤ s+1 := by omega
      obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hj2
      have hp : 8*prim (s+1) (target (s+1) (j+1) w)=15*den (s+1) := by
        rw [show target (s+1) (j+1) w = 8*((2:S (s+1))^n*
            (1+QuadraticAlgebra.omega)+2^(n+1)*w) by rw [hn]; unfold target; ring]
        exact primitive_eight _ hs3 _
      have ht := ih s hj2 (by omega) (truncate s w)
      calc
        _ = (8*prim (s+1) (target (s+1) (j+1) w))*(2*16^j) +
            1024*(16^j*count 6 (target s j (truncate s w))+2*den s) := by
              rw [pow_succ,den_succ]; ring
        _ = _ := by rw [hp,ht,pow_succ,den_succ]; ring

end RamDilate.Companion
#print axioms RamDilate.Companion.band
