import DilateCompanion

namespace RamDilate.Companion

/-- Reduction modulo the rational element 2 traps every square, and hence
every sum of squares, in the scalar subring. -/
theorem sum_mod_two_im_zero {d : ℕ} (x : Fin d → S 1) :
    (TargetOne.sqSum x).im = 0 := by
  unfold TargetOne.sqSum
  have h2 : (2 : ZMod (2^1)) = 0 := by decide
  have square_im_zero (z : S 1) : (z^2).im = 0 := by
    rw [pow_two, QuadraticAlgebra.im_mul]
    linear_combination (z.re*z.im)*h2
  have h (s : Finset (Fin d)) : (∑ i ∈ s, x i ^ 2).im = 0 := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, QuadraticAlgebra.im_add, square_im_zero, ih, add_zero]
  exact h Finset.univ

theorem no_companion_unit {d : ℕ} (x : Fin d → RamField.O) :
    TargetOne.sqSum x ≠ (1 + (QuadraticAlgebra.omega : RamField.O)) := by
  intro h
  have hp : RamField.digit 1 (QuadraticAlgebra.omega : RamField.O) = QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> first | exact map_zero _ | exact map_one _
  have hc := congrArg (RamField.digit 1) h
  simp only [TargetOne.sqSum, map_sum, map_pow, map_add, map_one, hp] at hc
  have hi := congrArg QuadraticAlgebra.im hc
  change (TargetOne.sqSum (fun i => RamField.digit 1 (x i))).im = 1 at hi
  exact (by decide : (0 : ZMod (2^1)) ≠ 1)
    ((sum_mod_two_im_zero _).symm.trans hi)

end RamDilate.Companion

#print axioms RamDilate.Companion.no_companion_unit
