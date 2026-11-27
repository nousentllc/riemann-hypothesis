import DilateCompanionCore
import DilateLowCompanion
import DilateEndpoint

noncomputable section
namespace RamDilate

theorem companion_pair (k : ℕ) (hk : 1≤k) :
    TargetOne.count 6 ((4:S (2*k+1))^k) +
      TargetOne.count 6 ((4:S (2*k+1))^k*(1+QuadraticAlgebra.omega)) = 4*den (2*k+1) := by
  have h := Companion.pair_counts (j := 2*k) (hj := by omega)
    (by
      rw [Companion.child,show (2:S 3)^2=4 by norm_num,low3_four,low3_four_companion]
      decide +kernel)
    (by
      rw [Companion.child,show (2:S 4)^3=8 by norm_num,low4_eight,low4_eight_companion]
      decide +kernel)
  have p : (2 : S (2*k+1))^(2*k) = 4^k := by rw [pow_mul]; norm_num
  simpa only [Companion.child,p] using h

/-- The nonsquare unit 1+π produces an equal and opposite deviation, here
proved at the first precision resolving the positive square-family density. -/
theorem companion_count (k : ℕ) (hk : 1≤k) :
    256^k*TargetOne.count 6 ((4:S (2*k+1))^k*(1+QuadraticAlgebra.omega)) =
      (2*256^k-2)*den (2*k+1) := by
  have transport (r : ℕ) (hr : r=0+(2*k+1)) :
      256^k*TargetOne.count 6 ((4:S r)^k) = (2*256^k+2)*den r := by
    subst r; exact counts k hk 0
  have p := transport (2*k+1) (by omega)
  have q := congrArg (fun z : ℕ => 256^k*z) (companion_pair k hk)
  simp only [Nat.mul_add] at q
  rw [p,Nat.add_mul] at q
  rw [Nat.sub_mul]
  have ha : 256^k*(4*den (2*k+1)) = 2*((2*256^k)*den (2*k+1)) := by ring
  rw [ha] at q
  omega

end RamDilate
#print axioms RamDilate.companion_count
