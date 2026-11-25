import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory IsDedekindDomain
open GlobalTheory.CompanionTheory.SW
open scoped TensorProduct

noncomputable section
namespace DyadicFiber

/-- A Gram fiber family in the original formalization vanishes at singular targets. -/
theorem singular_mass_zero {F E R : Type} [Field F] [Field E] [Algebra F E]
    [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n μ ν m) (S : HermR R σ n)
    (h : ¬ IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) : m S = 0 := by
  have hempty : gramR R σ J ⁻¹' {(S : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩
      {X | IsUnit (gramR R σ J X).det} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨heq, hu⟩
    change gramR R σ J X = _ at heq
    exact h (heq ▸ hu)
  have hzero := hm.1 S
  rw [hempty, Set.compl_empty] at hzero
  exact Measure.measure_univ_eq_zero.mp hzero

/-- For n=1 the ordinary nontriviality of the tensor algebra suffices at zero. -/
theorem zero_scalar_mass {F E R : Type} [Field F] [Field E] [Algebra F E]
    [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [Nontrivial (R ⊗[F] E)] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J 1 μ ν m) : m (hermScal R σ 0) = 0 := by
  apply singular_mass_zero σ J μ ν m hm
  rw [Matrix.det_fin_one]
  simp [hermScal]

abbrev Gaussian (K : Type) [Field K] := QuadraticAlgebra K (-1) 0

/-- Identity Hermitian form in Gaussian coordinates, using the source hform itself. -/
theorem gaussian_gram {K : Type} [Field K] (z : Fin 3 → Gaussian K) :
    hform (starRingEnd (Gaussian K)) (1 : Matrix (Fin 3) (Fin 3) (Gaussian K)) z z =
      algebraMap K (Gaussian K) (∑ j, ((z j).re ^ 2 + (z j).im ^ 2)) := by
  classical
  simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (z j).norm = (z j).re ^ 2 + (z j).im ^ 2 := by
    rw [QuadraticAlgebra.norm_def]
    ring
  rw [← hn, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  change star (z j) * z j = z j * star (z j)
  exact mul_comm _ _

/-- The half trace on a scalar is exactly that scalar, also at 2. -/
theorem half_trace_scalar {K : Type} [Field K] [CharZero K] (s : K) :
    (2 : K)⁻¹ * Algebra.trace K (Gaussian K) (algebraMap K (Gaussian K) s) = s := by
  rw [Algebra.trace_algebraMap, QuadraticAlgebra.finrank_eq_two]
  ring_nf

abbrev twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
local instance : Fact (Nat.Prime (twoPrime : ℕ)) := ⟨Nat.prime_two⟩

/-- The canonical equivalence links the chosen integral lattices as well as the fields. -/
theorem integer_transport (x : ℤ_[twoPrime]) :
    (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) twoPrime x) :
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm twoPrime).adicCompletion ℚ)) =
        Padic.adicCompletionEquiv (𝓞 ℚ) twoPrime x := by
  exact PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) twoPrime x

end DyadicFiber
#print axioms DyadicFiber.singular_mass_zero
#print axioms DyadicFiber.gaussian_gram
#print axioms DyadicFiber.half_trace_scalar
#print axioms DyadicFiber.integer_transport

#print axioms DyadicFiber.zero_scalar_mass
