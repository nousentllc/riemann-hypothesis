import New.Reduction.Zeros.PrimeError

open Complex DirichletCharacter New
noncomputable section
namespace Architecture

private def eulerFactor (p : ℕ) (s : ℂ) : ℂ := 1 - (p : ℂ) ^ (-s)

private theorem factor_at_one {p : ℕ} (hp : p.Prime) : eulerFactor p 1 ≠ 0 := by
  rw [eulerFactor, Complex.cpow_neg_one]
  intro he
  have h : (p : ℂ)⁻¹ = 1 := (sub_eq_zero.mp he).symm
  have hp_one : (p : ℂ) = 1 := inv_eq_one.mp h
  exact hp.ne_one (by exact_mod_cast hp_one)

private theorem factor_deriv {p : ℕ} (hp : p.Prime) :
    HasDerivAt (eulerFactor p) ((p : ℂ)⁻¹ * Complex.log p) 1 := by
  have h := (Complex.hasStrictDerivAt_const_cpow (x := (p : ℂ)) (y := (-1 : ℂ))
    (Or.inl (by exact_mod_cast hp.ne_zero))).hasDerivAt.comp (1 : ℂ) (hasDerivAt_id (1 : ℂ)).neg
  rw [Complex.cpow_neg_one] at h
  change HasDerivAt (fun s : ℂ => (1 : ℂ) - (p : ℂ) ^ (-s)) _ _
  simpa [Function.comp_def] using h.const_sub (1 : ℂ)

/-- The correction to conductor-one centering at any modulus, in real Euler factors. -/
theorem principal_center_euler (q : ℕ) [NeZero q] :
    (logDeriv (entireL (1 : DirichletCharacter ℂ q)) 1).re - Real.eulerMascheroniConstant =
    ∑ p ∈ q.primeFactors, Real.log p / (p - 1) := by
  let F : ℂ → ℂ := ∏ p ∈ q.primeFactors, eulerFactor p
  have hE : entireL (1 : DirichletCharacter ℂ q) = F * riemannZeta₁ := by
    funext s
    by_cases h : s = 1
    · subst s
      simp [entireL, DirichletCharacter.LFunctionTrivChar₁, F, eulerFactor, Complex.cpow_neg_one]
    · rw [show entireL (1 : DirichletCharacter ℂ q) s = (s-1)*LFunctionTrivChar q s by
            simp [entireL, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h],
          LFunctionTrivChar_eq_mul_riemannZeta h, riemannZeta_eq_inv_sub_mul h, Pi.mul_apply]
      simp [F, eulerFactor, field]
  have hf : F 1 ≠ 0 := by
    simpa [F, Finset.prod_apply] using Finset.prod_ne_zero_iff.2
      (fun p (hp : p ∈ q.primeFactors) => factor_at_one (Nat.prime_of_mem_primeFactors hp))
  have hd : DifferentiableAt ℂ F 1 := by
    simpa [F, Finset.prod_apply] using DifferentiableAt.finsetProd
      (u := q.primeFactors) (fun p hp => (factor_deriv (Nat.prime_of_mem_primeFactors hp)).differentiableAt)
  rw [hE, logDeriv_mul 1 hf (by simp) hd (differentiable_riemannZeta₁ 1)]
  have hF : logDeriv F 1 = ∑ p ∈ q.primeFactors, (Real.log p / ((p:ℝ)-1) : ℝ) := by
    rw [show F = ∏ p ∈ q.primeFactors, eulerFactor p from rfl,
        logDeriv_prod (fun p hp => factor_at_one (Nat.prime_of_mem_primeFactors hp))
          (fun p hp => (factor_deriv (Nat.prime_of_mem_primeFactors hp)).differentiableAt)]
    push_cast
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have h0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have h1 : (p:ℂ) ≠ 1 := by exact_mod_cast hp'.ne_one
    rw [logDeriv_apply, (factor_deriv hp').deriv]
    rw [eulerFactor, Complex.cpow_neg_one]
    have hfac : 1 - (p:ℂ)⁻¹ ≠ 0 := by simpa only [eulerFactor, Complex.cpow_neg_one] using factor_at_one hp'
    field_simp [h0, sub_ne_zero.2 h1, hfac]
  rw [hF, Complex.add_re, Complex.ofReal_re]
  simp [logDeriv_apply]
end Architecture
#print axioms Architecture.principal_center_euler
