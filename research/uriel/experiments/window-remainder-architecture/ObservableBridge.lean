import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
import New.Reduction.Zeros.PrimeError
import Euler

open Complex Finset Nat ArithmeticFunction DirichletCharacter New
open ArithmeticFunction.vonMangoldt
noncomputable section
namespace Architecture

variable {q : ℕ} [NeZero q]
def raw (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (χ n).re * (1 / (n : ℝ) - 1 / y)⁺

omit [NeZero q] in
theorem ramp_raw (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 0 < y) :
    (Deduction.ramp (fun n => χ n) y).re = y * raw χ y := by
  classical
  have hz : (Icc 1 ⌊y⌋₊ : Finset ℕ) = (range (⌊y⌋₊+1)).erase 0 := by
    ext n
    simp only [mem_Icc, mem_erase, mem_range]
    omega
  have hk (n : ℕ) : max (y / (n:ℝ) - 1) 0 = y * (1 / (n:ℝ) - 1 / y)⁺ := by
    rw [posPart_def, mul_max_of_nonneg _ _ hy.le, mul_zero, mul_sub]
    simp [div_eq_mul_inv,hy.ne']
  unfold Deduction.ramp raw
  rw [Complex.re_sum, hz, sum_erase_eq_sub (by simp)]
  simp only [ArithmeticFunction.map_zero, zero_mul, sub_zero]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro n _
  simp [Complex.mul_re,hk]
  ring

def principalDefect (q : ℕ) [NeZero q] : ℝ :=
  (logDeriv (entireL (1 : DirichletCharacter ℂ q)) 1).re - Real.eulerMascheroniConstant

theorem old_center (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 0 < y) :
    (Deduction.Gchi χ y).re / y = raw χ y + (logDeriv (entireL χ) 1).re +
      (if χ = 1 then 1 - Real.log y - principalDefect q else 0) := by
  classical
  by_cases h : χ = 1
  · subst χ
    simp [Deduction.Gchi, principalDefect, ramp_raw _ hy, field]
    ring
  · simp only [Deduction.Gchi, ite_eq_right h, add_re, ramp_raw _ hy, entireL, logDeriv,
      Pi.div_apply, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    field_simp

theorem weight (d : ℕ) [Fact d.Prime] (n : ℕ) :
    lambdaKResidueClass d q n * (φ q : ℝ) =
      ∑ ψ : DirichletCharacter ℂ q, (ArithmeticFunction.vonMangoldt n : ℝ) * ((ψ n).re - (quadTwist ψ d n).re) := by
  let a (ψ : DirichletCharacter ℂ q) : ℕ → ℂ :=
    (fun n : ℕ ↦ ψ n * vonMangoldt n) - fun n : ℕ ↦ quadTwist ψ d n * vonMangoldt n
  have ht (ψ : DirichletCharacter ℂ q) : quadTwist ψ d n = ψ n * legendreSym d n :=
    mod_cast quadTwist_apply ψ d n
  have hc : (lambdaKResidueClass d q n : ℂ) = ((φ q : ℂ)⁻¹ • ∑ ψ : DirichletCharacter ℂ q, a ψ) n := by
    simp [a,lambdaKResidueClass,chiK_eq_legendreSym,residueClass_apply,ht,←sum_mul,field]
  have hφ : (φ q : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have hh : (φ q : ℂ) * (lambdaKResidueClass d q n : ℂ) = ∑ ψ : DirichletCharacter ℂ q, a ψ n := by
    rw [hc, Pi.smul_apply, smul_eq_mul, ←mul_assoc, mul_inv_cancel₀ hφ, one_mul, Finset.sum_apply]
  simpa [a, Complex.mul_re, Complex.re_sum, mul_sub, mul_comm] using congrArg Complex.re hh

theorem raw_sum (d : ℕ) [Fact d.Prime] {y : ℝ} :
    (∑ n ∈ Icc 1 ⌊y⌋₊, lambdaKResidueClass d q n * (1/(n:ℝ)-1/y)⁺) * φ q =
      ∑ ψ : DirichletCharacter ℂ q, (raw ψ y - raw (quadTwist ψ d) y) := by
  classical
  simp only [raw, ←sum_sub_distrib]
  rw [sum_comm (s:=univ) (t:=Icc 1 ⌊y⌋₊), sum_mul]
  apply sum_congr rfl
  intro n _
  rw [mul_right_comm,weight, sum_mul]
  apply sum_congr rfl
  intro ψ _
  ring

/-- The exact dictionary on the main modulus as well as the auxiliary modulus. -/
theorem centered_dictionary (d : ℕ) [Fact d.Prime] (hd : d ≠ 2) (hcop : q.Coprime d)
    {y : ℝ} (hy : 0 < y) :
    (φ q : ℝ) * primeRemainder d q y =
      (∑ ψ : DirichletCharacter ℂ q, ((Deduction.Gchi ψ y).re/y -
        (Deduction.Gchi (quadTwist ψ d) y).re/y)) + principalDefect q := by
  classical
  have hφ : (φ q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have hlog : (φ q : ℝ) * (Real.log y / (φ q : ℝ)) = Real.log y := by
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hφ, mul_one]
  have hmean : (φ q : ℝ) * (logDerivMean d q 1).re =
      (∑ ψ : DirichletCharacter ℂ q, ((logDeriv (entireL (quadTwist ψ d)) 1).re -
        (logDeriv (entireL ψ) 1).re)) - 1 := by
    have hh : (φ q : ℂ) * logDerivMean d q 1 =
        (∑ ψ : DirichletCharacter ℂ q, (logDeriv (entireL (quadTwist ψ d)) 1 -
          logDeriv (entireL ψ) 1)) - 1 := by
      have hC : (φ q : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
      rw [logDerivMean, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hC, mul_one]
    simpa [Complex.mul_re, Complex.re_sum] using congrArg Complex.re hh
  rw [primeRemainder_eq_sum_posPart (d:=d) (q:=q) hy (le_refl _)]
  simp_rw [old_center _ hy, ite_eq_right (quadTwist_ne_one _ d hd hcop), add_zero]
  rw [mul_sub, mul_sub, mul_comm (φ q : ℝ) (∑ _ ∈ Icc 1 ⌊y⌋₊, _), raw_sum, hmean, hlog]
  simp [sum_sub_distrib, sum_add_distrib, field]
  ring

theorem principalDefect_one : principalDefect 1 = 0 := by
  have hz : entireL (1 : DirichletCharacter ℂ 1) = riemannZeta₁ := by
    have h (s : ℂ) (hs : s ≠ 1) : (s - 1) * riemannZeta s = riemannZeta₁ s := by
      rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]
    simpa [entireL, Function.update_eq_iff] using h
  simp [principalDefect, hz, logDeriv]

/-- The signed comparison in terms of a computable finite set of primes. -/
theorem centered_dictionary_euler (d : ℕ) [Fact d.Prime] (hd : d ≠ 2) (hcop : q.Coprime d)
    {y : ℝ} (hy : 0 < y) :
    (φ q : ℝ) * primeRemainder d q y =
      (∑ ψ : DirichletCharacter ℂ q, ((Deduction.Gchi ψ y).re/y -
        (Deduction.Gchi (quadTwist ψ d) y).re/y)) +
      ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1) := by
  rw [centered_dictionary d hd hcop hy, principalDefect, principal_center_euler]

end Architecture
#print axioms Architecture.centered_dictionary_euler
#print axioms Architecture.principalDefect_one
#print axioms Architecture.ramp_raw
#print axioms Architecture.centered_dictionary
