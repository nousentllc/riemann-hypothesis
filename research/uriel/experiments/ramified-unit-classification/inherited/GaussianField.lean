import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField HeckeCharacterZeroLocus.SiegelWeilU
noncomputable section
namespace TargetOne
abbrev E := QuadraticAlgebra ℚ (-1) 0
instance gaussIrred : Fact (∀ r : ℚ, r^2 ≠ -1 + 0*r) := ⟨fun r h => by nlinarith [sq_nonneg r]⟩
instance gaussNumberField : NumberField E := {}
def conjG : E →ₐ[ℚ] E := (starRingEnd E).toRatAlgHom
abbrev ii : E := QuadraticAlgebra.omega
theorem ii_sq : ii^2=(-1 : E) := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl
theorem isCM : IsCMExt ℚ E conjG := by
  refine ⟨inferInstance,⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => ?_⟩,
    QuadraticAlgebra.finrank_eq_two _ _,?_⟩
  · let f := InfinitePlace.embedding_of_isReal hv
    have h := congrArg f ii_sq
    simp only [map_pow,map_neg,map_one] at h
    nlinarith [sq_nonneg (f ii)]
  · intro τ x
    have hi : (τ ii)^2=(-1 : ℂ) := by rw [←map_pow,ii_sq,map_neg,map_one]
    have hI : τ ii = Complex.I ∨ τ ii = -Complex.I := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [hi,Complex.I_sq]
    have hc : star (τ ii) = -τ ii := by
      rcases hI with h|h <;> rw [h] <;> simp
    obtain ⟨a,b⟩ := x
    change τ (star (⟨a,b⟩ : E)) = _
    have hs : star (⟨a,b⟩ : E) = ⟨a,-b⟩ := by ext <;> simp
    rw [hs,QuadraticAlgebra.mk_eq_add_smul_omega,QuadraticAlgebra.mk_eq_add_smul_omega a b,
      Algebra.smul_def,Algebra.smul_def]
    change τ (algebraMap ℚ E a + algebraMap ℚ E (-b) * ii) = star (τ (algebraMap ℚ E a + algebraMap ℚ E b * ii))
    simp [hc] 
theorem herm_id : IsHermND conjG (1 : Matrix (Fin 3) (Fin 3) E) := by
  constructor
  · intro i j; by_cases h : i=j <;> simp [Matrix.one_apply,h,Ne.symm]
  · simp
end TargetOne
#print axioms TargetOne.isCM
