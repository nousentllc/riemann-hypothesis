import Contact
import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresTransitivityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableCoordinateMapsTensorStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace TargetOne

theorem local_mass_from_tests {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (Bv : Matrix (Fin M × Fin d) (Fin M × Fin d) (Fv F v))
    (hform : ∀ x y : Fin M → Fv F v ⊗[F] E,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y) =
        (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr (x p.1) p.2) ⬝ᵥ
          (Bv *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr (y p.1) p.2))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m)
    (s : Fv F v) (D : ℝ≥0)
    (U : Set (Fv F v)) (hU : IsOpen U) (hsU : s ∈ U) (hregular : ∀ z ∈ U, z ≠ 0)
    (hloc : IsLocR (Fv F v))
    (hLc : IsCompact (latV (M := M) (n := 1) b v)) (hLo : IsOpen (latV (M := M) (n := 1) b v))
    (hD : ∀ N ∈ 𝓝 s, ∃ C : Set (Fv F v), IsCompact C ∧ C ⊆ U ∩ N ∧ 0 < lam.real C ∧
      (Measure.pi fun _ : Fin M × Fin d => lam)
        {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} =
        (D : ℝ≥0∞) * lam C) :
    (m (hermScal (Fv F v) σ s) (latV b v)).toReal = D := by
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, -, -, hBorW, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hSh, hSl, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  obtain ⟨-, -, -, hHB, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) 1
  obtain ⟨g, -, hgram⟩ := hG M J hJ
  obtain ⟨hcm, hcmap⟩ := GlobalTheory.T.measurable_coordinate_maps_tensor F E σ hCM (Fv F v) d b M lam hlam.1
  haveI : BorelSpace (Fin 1 → Fin M → Fv F v ⊗[F] E) := hBorW 1 M
  haveI : BorelSpace (HermR (Fv F v) σ 1) := hHB
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet
  obtain ⟨c, hcdef⟩ : ∃ c : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin M × Fin d → Fv F v),
      c = fun X p => (Algebra.TensorProduct.basis (Fv F v) b).repr (X 0 p.1) p.2 := ⟨_, rfl⟩
  rw [← hcdef] at hcm hcmap
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := M) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, hgi⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM M J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hinj : Function.Injective (hermScal (Fv F v) σ) := hSh.injective
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  have hunit : ∀ z ∈ U,
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    have hz0 : z ≠ 0 := hregular z hz
    have hu : IsUnit (algebraMap (Fv F v) (Fv F v ⊗[F] E) z) := (IsUnit.mk0 z hz0).map _
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    simpa [hermScal, Algebra.TensorProduct.algebraMap_apply] using hu
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal)
      U := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  have hkey : ∀ C : Set (Fv F v), IsCompact C → C ⊆ U →
      (Measure.pi fun _ : Fin M × Fin d => lam)
        {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} =
        (D : ℝ≥0∞) * lam C →
      ∫ z in C, (m (hermScal (Fv F v) σ z) (latV b v)).toReal ∂lam = ((D : ℝ≥0∞) * lam C).toReal := by
    intro C hC hCB hcalc
    have hCm : MeasurableSet C := hC.measurableSet
    have hsub : hermScal (Fv F v) σ '' C ⊆
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hunit z (hCB hz)
    have e : ∫ X in gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C)), φ X
          ∂(coordW (Fv F v) b lam 1 M) =
        ∫ T in hermScal (Fv F v) σ '' C, ∫ X, φ X ∂(m T) ∂(coordHerm (Fv F v) σ b lam 1) :=
      hgi _ (hC.image hSh.continuous) hsub
    have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
      (Valued.isOpen_valuationSubring _).measurableSet
    have hTm : MeasurableSet {x : Fin M × Fin d → Fv F v |
        (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} := by
      have h1 : MeasurableSet {x : Fin M × Fin d → Fv F v |
          ∀ i, x i ∈ v.adicCompletionIntegers F} := by
        have : {x : Fin M × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
            ⋂ i, (fun x : Fin M × Fin d → Fv F v => x i) ⁻¹'
              (v.adicCompletionIntegers F : Set (Fv F v)) := by
          ext x; simp
        rw [this]
        exact MeasurableSet.iInter fun i => measurable_pi_apply i hO
      have hq : Continuous fun x : Fin M × Fin d → Fv F v =>
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) :=
        continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
      exact h1.inter (hq.measurable hC.isClosed.measurableSet)
    have hset : (gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C))) ∩ latV b v =
        c ⁻¹' {x : Fin M × Fin d → Fv F v |
          (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (Bv *ᵥ x)) ∈ C} := by
      ext X
      have hgX := hgram X
      have hQ : hermScal (Fv F v) σ ((2 : Fv F v)⁻¹ * (c X ⬝ᵥ (Bv *ᵥ c X))) = g X := by
        have h1 := hSl (g X)
        have h2 : ((g X : HermR (Fv F v) σ 1) : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) 0 0 =
            hR (Fv F v) σ J (X 0) (X 0) := by
          rw [← hgX]; rfl
        have h3 : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
          rw [one_div, map_inv₀, map_ofNat]
        rw [h2, hform, h3] at h1
        rw [hcdef]
        exact h1
      constructor
      · rintro ⟨⟨T, ⟨z, hz, rfl⟩, hT⟩, hL⟩
        refine ⟨fun p => ?_, ?_⟩
        · rw [hcdef]; exact hL 0 p.1 p.2
        · have h1 : hermScal (Fv F v) σ z = g X := Subtype.ext (hT.trans hgX)
          rw [← hinj (h1.trans hQ.symm)]
          exact hz
      · rintro ⟨hi, hq⟩
        refine ⟨⟨g X, ⟨_, hq, hQ⟩, hgX.symm⟩, fun a i k => ?_⟩
        obtain rfl : a = 0 := Subsingleton.elim _ _
        have := hi (i, k)
        rw [hcdef] at this
        exact this
    have hmass : coordW (Fv F v) b lam 1 M
        ((gramR (Fv F v) σ J ⁻¹' (Subtype.val '' (hermScal (Fv F v) σ '' C))) ∩ latV b v) =
        (D : ℝ≥0∞) * lam C := by
      rw [hset, ← Measure.map_apply hcm hTm, hcmap]
      exact hcalc
    rw [hφ, setIntegral_indicator hLm, setIntegral_const, ← hφ, ← hSm lam hlam.1,
      hEmb.setIntegral_map, Set.preimage_image_eq _ hinj] at e
    simp_rw [hval] at e
    rw [integral_complex_ofReal, Measure.real, hmass, Complex.real_smul, mul_one] at e
    exact (Complex.ofReal_injective e).symm
  apply contact lam U hU hsU _ hcont
  intro N hN
  obtain ⟨C,hC,hsub,hpos,hcalc⟩ := hD N hN
  refine ⟨C,hC,hsub,hpos,?_⟩
  rw [hkey C hC (hsub.trans Set.inter_subset_left) hcalc, ENNReal.toReal_mul]
  rfl
end TargetOne
#print axioms TargetOne.local_mass_from_tests
