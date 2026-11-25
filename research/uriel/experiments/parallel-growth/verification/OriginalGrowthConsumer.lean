import GrowthConsumer
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

/-! This bridge uses the original finite fiber product, the archimedean test integral,
the adelic theta measure, and the Euler-product predicate of the pinned source. -/
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField
open IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GrowthConsumer

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
variable (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
variable (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
variable (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 →
  Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
variable (β : F) (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ)

abbrev inputBox (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) :
    Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}

abbrev finiteProduct (a : ℕ) : ℝ :=
  ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (inputBox b v a)).toReal

abbrev archWeight : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β)))

abbrev thetaFiberMeasure : Measure (Fin 1 → Fin M → AF F ⊗[F] E) :=
  thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}

abbrev thetaIntegral (a : ℕ) : ℝ≥0∞ :=
  ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ inputBox b v a},
    ENNReal.ofReal (φ (projInf X)) ∂(thetaFiberMeasure σ J μ 𝓕 β)

abbrev scalarEuler (c : ℝ≥0) : Prop :=
  IsEulerProd b (thetaFiberMeasure σ J μ 𝓕 β) c
    (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))

/-- The nonzero branch, at a fixed original scalar fiber. The three premises below the
prior Euler normalization are precisely a growth bound, a theta discrepancy test,
and the Euler evaluation of the same test set. -/
theorem original_scalar_comparison (hM : 3 ≤ M) {κ C : ℝ} {c : ℝ≥0}
    (hc : scalarEuler σ J b μ 𝓕 mi m β c)
    (hi : mi (hermScal (Ainf F) σ (algebraMap F _ β)) ≠ 0)
    (hφm : Measurable fun X => ENNReal.ofReal (φ X)) (hφpos : ∀ X, 0 < φ X)
    (hfin : archWeight σ mi β φ < ⊤) (hκ : 0 < κ)
    (grow : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤
      finiteProduct σ b m β a)
    (test : ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0,
      thetaIntegral σ J b μ 𝓕 β φ a = (I : ℝ≥0∞) ∧
      |(I : ℝ) - (archWeight σ mi β φ).toReal * finiteProduct σ b m β a| ≤
        C*(a : ℝ)^(Module.finrank ℚ F*M))
    (evaluate : ∀ a : ℕ, 0 < a → thetaIntegral σ J b μ 𝓕 β φ a =
      (c : ℝ≥0∞) * archWeight σ mi β φ * ENNReal.ofReal (finiteProduct σ b m β a)) :
    c = 1 ∧ scalarEuler σ J b μ 𝓕 mi m β 1 := by
  have hw : 0 < (archWeight σ mi β φ).toReal := ENNReal.toReal_pos (fun h => hi (by
    rw [archWeight, lintegral_eq_zero_iff hφm] at h
    exact ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 (h.mono fun X hX =>
      (ENNReal.ofReal_pos.2 (hφpos X)).ne' hX)))) hfin.ne
  have h : c = 1 := rank_one_comparison Module.finrank_pos hM hw hκ
    (finiteProduct σ b m β) grow (fun a ha hP => by
      obtain ⟨I,hI,herr⟩ := test a ha
      have eq := congrArg ENNReal.toReal (hI.symm.trans (evaluate a ha))
      rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hP,
          ENNReal.coe_toReal,ENNReal.coe_toReal] at eq
      exact ⟨(I : ℝ),eq,herr⟩)
  exact ⟨h, h ▸ hc⟩

/-- Any positive starting value and positive step multiplier give the cofinal
witnesses required above. The same finite product function is passed through. -/
theorem cofinal_of_progression {N Q p : ℕ} (hN : 0 < N) (hQ : 0 < Q) (κ : ℝ)
    (P : ℕ → ℝ) (lower : ∀ j : ℕ,
      κ * ((N*(1+j*Q) : ℕ) : ℝ)^p ≤ P (N*(1+j*Q))) :
    ∀ k : ℕ, ∃ a : ℕ, k<a ∧ κ*(a : ℝ)^p ≤ P a := by
  intro k
  have first : k ≤ k*Q := Nat.le_mul_of_pos_right k hQ
  have last : 1 + k*Q ≤ N*(1+k*Q) := Nat.le_mul_of_pos_left _ hN
  exact ⟨N*(1+k*Q),by omega,lower k⟩

end GrowthConsumer
#print axioms GrowthConsumer.original_scalar_comparison
#print axioms GrowthConsumer.cofinal_of_progression
