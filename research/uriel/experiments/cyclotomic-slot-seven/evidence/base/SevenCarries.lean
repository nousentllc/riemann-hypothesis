import Mathlib.Tactic

namespace SlotSevenCarry

/-- Lifting one factor of seven retains a unit congruent to one. -/
theorem unitStep (a d : ℤ) (h : a + 1 = 7*d) :
    ∃ w : ℤ, a^7+1 = 49*d*(1+7*w) := by
  have ha : a = 7*d-1 := by linarith
  refine ⟨-3*d + 35*d^2 - 245*d^3 + 1029*d^4 - 2401*d^5 + 2401*d^6, ?_⟩
  rw [ha]
  ring

/-- The denominator of the normalized formula at every seven-power conductor. -/
theorem denominatorUnit (k : ℕ) :
    ∃ b : ℤ, (3:ℤ)^(3*7^k)+1 = (7:ℤ)^(k+1)*(4+7*b) := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨b,hb⟩ := ih
    have old : (3:ℤ)^(3*7^k)+1 = 7*((7:ℤ)^k*(4+7*b)) := by
      rw [hb,pow_succ]
      ring
    obtain ⟨w,hw⟩ := unitStep _ _ old
    refine ⟨b+4*w+7*b*w, ?_⟩
    rw [show 3*7^(k+1) = 3*7^k*7 by rw [pow_succ]; ring, pow_mul, hw]
    rw [pow_succ (7:ℤ) (k+1), pow_succ (7:ℤ) k]
    ring

/-- The three reduced roots support three nonzero character evaluations. -/
theorem residueCertificate :
    (Finset.univ.filter (fun z : ZMod 7 => z^3+1=0)) = {3,5,6} ∧
    (-2*(1+(3:ZMod 7)^2)=1 ∧ -2*(1+(5:ZMod 7)^2)=4 ∧
      -2*(1+(6:ZMod 7)^2)=3 ∧ (1*4*3 : ZMod 7)=5) := by decide

#print axioms unitStep
#print axioms denominatorUnit
#print axioms residueCertificate
end SlotSevenCarry
