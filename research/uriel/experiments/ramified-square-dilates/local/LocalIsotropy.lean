import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormulaStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace LocalIsotropy

theorem matrix_isotropic_at_finite_place {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hi : 5 ≤ Fintype.card ι) (B : Matrix ι ι (Fv F v)) :
    ∃ x : ι → Fv F v, x ≠ 0 ∧ x ⬝ᵥ (B *ᵥ x) = 0 := by
  classical
  letI : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero
  let Q := B.toQuadraticForm'
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hdim : 5 ≤ Fintype.card (Fin (Module.finrank (Fv F v) (ι → Fv F v))) := by simpa using hi
  obtain ⟨y, hy, hyq⟩ := GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le F v hdim w
  refine ⟨e.symm y, fun h => hy ?_, ?_⟩
  · simpa using congrArg e h
  · have hq := e.symm.map_app y
    simpa [Q, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply',
      QuadraticMap.weightedSumSquares_apply, smul_eq_mul, ← sq, hyq] using hq

/-- The original CM trace form has a nonzero regular zero at every finite
completion once the Hermitian rank is at least three. The witness includes an
actual rank-one Gram tuple and an explicit nonzero coordinate covector. -/
theorem regular_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (hM : 3 ≤ M)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F) (X : Fin 1 → Fin M → Fv F v ⊗[F] E),
      B.IsSymm ∧ B.det ≠ 0 ∧ X ≠ 0 ∧ gramR (Fv F v) σ J X 0 0 = 0 ∧
        B.map (algebraMap F (Fv F v)) *ᵥ TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) (X 0) ≠ 0 ∧
        (∀ y z : Fin M → Fv F v ⊗[F] E,
          Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J y z) =
            TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) y ⬝ᵥ
              (B.map (algebraMap F (Fv F v)) *ᵥ TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) z)) := by
  classical
  obtain ⟨B, hB, hd, -, hlocal⟩ := GlobalTheory.T.exists_trace_form_gram_matrix_in_basis
    F E σ hσ M J hJ d b
  have hd2 : d = 2 := by simpa [Module.finrank_eq_card_basis b] using hσ.2.2.1
  have hc : 5 ≤ Fintype.card (Fin M × Fin d) := by simp [hd2]; omega
  obtain ⟨u, hu, hz⟩ := matrix_isotropic_at_finite_place v hc (B.map (algebraMap F (Fv F v)))
  let β := Algebra.TensorProduct.basis (Fv F v) b
  obtain ⟨x, hx⟩ := TraceCoord.coord_surj β u
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hu
    rw [← hx]
    ext i
    simp [TraceCoord.coord]
  have hf := (hlocal (Fv F v)).1
  change ∀ x y, _ = TraceCoord.coord β x ⬝ᵥ (_ *ᵥ TraceCoord.coord β y) at hf
  refine ⟨B, fun _ => x, hB, hd, fun he => hx0 (congrFun he 0), ?_, ?_, hf⟩
  · have htr := hf x x
    rw [hx, hz] at htr
    have hg := FibreRatio.gram_entry (Fv F v) hσ hJ (fun _ : Fin 1 => x)
    change (gramR (Fv F v) σ J (fun _ : Fin 1 => x) 0 0) = (_ * Algebra.trace _ _ (hR _ _ _ x x)) ⊗ₜ[F] _ at hg
    simpa [htr] using hg
  · change B.map _ *ᵥ TraceCoord.coord β x ≠ 0
    rw [hx]
    intro hzero
    apply hu (Matrix.eq_zero_of_mulVec_eq_zero ?_ hzero)
    exact (RingHom.map_det (algebraMap F (Fv F v)) B) ▸ (map_ne_zero _).2 hd

end LocalIsotropy
#print axioms LocalIsotropy.matrix_isotropic_at_finite_place
#print axioms LocalIsotropy.regular_zero
