import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
import RamField

open scoped ArithmeticFunction.vonMangoldt
open Complex

noncomputable section
namespace NousInterface

/-- Scalar kernel identity, including the Lean convention for division by zero at n = 0. -/
theorem ramp_kernel (y r : ℝ) (hy : 0 < y) :
    max (y / r - 1) 0 = y * max (1 / r - 1 / y) 0 := by
  rw [mul_max_of_nonneg _ _ hy.le, mul_zero, mul_sub]
  congr 1
  simp [div_eq_mul_inv, hy.ne']

/-- Put the original complex ramp on the scale of the new real remainder. -/
theorem ramp_re (f : ℕ → ℂ) (y : ℝ) (hy : 0 < y) :
    (Deduction.ramp f y).re = y * ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
      (Λ n : ℝ) * (f n).re * max (1 / (n : ℝ) - 1 / y) 0 := by
  rw [Deduction.ramp, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [ramp_kernel y (n : ℝ) hy]
  simp [Complex.mul_re]
  ring

/-- The centered signed contrast in the old vocabulary, with the q=1 real centering written out. -/
theorem centered_contrast {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (y : ℝ) (hy : 0 < y) :
    (Deduction.G y - (Deduction.Gchi χ y).re) / y =
      (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
        (Λ n : ℝ) * (1 - (χ n).re) * max (1 / (n : ℝ) - 1 / y) 0) -
      Real.log y + (1 + Real.eulerMascheroniConstant) -
      (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re := by
  rw [Deduction.G, Deduction.Gchi, if_neg hχ, Complex.add_re, ramp_re _ _ hy, ramp_re _ _ hy]
  rw [div_eq_iff hy.ne']
  simp only [Complex.one_re, mul_one, Complex.re_ofReal_mul]
  simp_rw [mul_sub, mul_one, sub_mul, Finset.sum_sub_distrib]
  ring

abbrev GaussianOrder := QuadraticAlgebra RamField.O (-1) 0

/-- Conjugation on the Gaussian coordinate order has trace in twice the coefficient order. -/
theorem trace_real (z : GaussianOrder) : (z + star z).re = 2 * z.re := by
  simp [QuadraticAlgebra.re_star, two_mul]

/-- No element of the exact Gaussian coordinate order used for the lattice has trace one. -/
theorem no_integral_trace_one (z : GaussianOrder) : z + star z ≠ 1 := by
  intro h
  have hreal := congrArg QuadraticAlgebra.re h
  rw [trace_real, QuadraticAlgebra.re_one] at hreal
  have hsum : z.re + z.re = 1 := by simpa only [two_mul] using hreal
  have hres := congrArg (fun x : RamField.O => PadicInt.toZModPow 1 x.re) hsum
  change PadicInt.toZModPow 1 (z.re.re + z.re.re) = PadicInt.toZModPow 1 1 at hres
  rw [map_add, map_one, ← two_mul] at hres
  have ht : (2 : ZMod (2^1)) = 0 := by decide
  rw [ht, zero_mul] at hres
  exact (by decide : (0 : ZMod (2^1)) ≠ 1) hres

/-- Necessary numerical consequence if the upstream lattice bound transported verbatim. -/
theorem four_exceeds_ceiling : ¬ (1 + |(257/128 : ℝ) - 1| ≤ 2) := by
  norm_num

/-- The same ceiling test accepts the smaller finite sibling value. -/
theorem lower_value_passes_ceiling : 1 + |(255/128 : ℝ) - 1| ≤ 2 := by
  norm_num

end NousInterface

#print axioms NousInterface.ramp_kernel
#print axioms NousInterface.ramp_re
#print axioms NousInterface.centered_contrast
#print axioms NousInterface.trace_real
#print axioms NousInterface.no_integral_trace_one
#print axioms NousInterface.four_exceeds_ceiling
#print axioms NousInterface.lower_value_passes_ceiling
