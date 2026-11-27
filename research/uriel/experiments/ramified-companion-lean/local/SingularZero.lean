import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Set
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace SingularZero

theorem singular_member {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (ν : Measure (HermR (Fv F v) σ n))
    (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J n μ ν m) (S : HermR (Fv F v) σ n)
    (hS : ¬IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det) :
    m S = 0 := by
  have h := hm.1 S
  have he : (gramR (Fv F v) σ J ⁻¹' {(S:Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩ {X | IsUnit (gramR (Fv F v) σ J X).det}) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨he, hu⟩
    exact hS ((Set.mem_singleton_iff.mp he) ▸ hu)
  simpa [he] using h

theorem rank_one_origin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (ν : Measure (HermR (Fv F v) σ 1))
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 μ ν m) : m (hermScal (Fv F v) σ 0) = 0 := by
  apply singular_member σ M 1 J v μ ν m hm
  rw [Matrix.det_fin_one]
  simp [hermScal]

end SingularZero
#print axioms SingularZero.rank_one_origin
