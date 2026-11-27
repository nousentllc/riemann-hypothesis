import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormulaStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace LocalTube

/-- If every neighborhood of a regular target contains a positive target test
whose tube has mass at least c times the base mass, the original Gram family
itself has at least c units of mass on the compact open domain. -/
theorem mass_lower_of_tubes {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M)
      (coordHerm (Fv F v) σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (s : Fv F v) (hs : s ≠ 0) (c : ℝ)
    (ht : ∀ U ∈ 𝓝 s, ∃ V : Set (Fv F v), MeasurableSet V ∧ V ⊆ U ∧ 0 < (lam V).toReal ∧
      c * (lam V).toReal ≤
        (coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) *
          Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal) :
    c ≤ (m (hermScal (Fv F v) σ s) A).toReal := by
  by_contra! h
  let ε := (c - (m (hermScal (Fv F v) σ s) A).toReal) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨U, hU, hratio⟩ := GlobalTheory.T.local_gram_fiber_rank_one_set_formula
    F E σ hσ M J hJ d b v lam hlam m hm A hAc hAo s hs ε hε
  obtain ⟨V, hV, hsub, hpos, hlower⟩ := ht U hU
  have hu := (abs_le.mp (hratio V hV hsub)).2
  have hh : (c - (m (hermScal (Fv F v) σ s) A).toReal) * (lam V).toReal ≤ ε * (lam V).toReal := by
    rw [sub_mul]; linarith
  have hh' := (mul_le_mul_iff_left₀ hpos).1 hh
  dsimp [ε] at hh'
  linarith

end LocalTube
#print axioms LocalTube.mass_lower_of_tubes
