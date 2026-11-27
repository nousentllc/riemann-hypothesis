import Mathlib
namespace DenominatorControl

/-- In Gaussian coordinates, integrality at two obstructs every odd multiplier
when the rational scalar target is 1/2. This proves the congruence obstruction;
the measure-theoretic support interpretation is discussed separately. -/
theorem odd_dilation_no_integral_solution (a : ℕ) (ha : Odd a) (x : Fin 6 → ℤ) :
    2 * (∑ i, x i ^ 2) ≠ (a:ℤ)^2 := by
  intro h
  have h' := congrArg (fun n : ℤ => (n : ZMod 2)) h
  obtain ⟨b,hb⟩ := ha
  have hz : (2 : ZMod 2) = 0 := by decide
  simp [hb,hz] at h'

/-- The same obstruction already holds in the residue ring, hence does not
require a global non-representation argument. -/
theorem no_solution_mod_two (x : Fin 6 → ZMod 2) :
    (2:ZMod 2) * (∑ i, x i ^ 2) ≠ 1 := by
  rw [show (2:ZMod 2) = 0 by decide, zero_mul]; decide

/-- A rational smooth representation of 1/2 still exists. -/
theorem represented : (1/2:ℚ)^2 + (1/2:ℚ)^2 = 1/2 := by norm_num

end DenominatorControl
#print axioms DenominatorControl.odd_dilation_no_integral_solution
#print axioms DenominatorControl.no_solution_mod_two
#print axioms DenominatorControl.represented
