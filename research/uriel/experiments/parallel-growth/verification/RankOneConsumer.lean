import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaFin
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainRankOneDensityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement

import OriginalGrowthConsumer

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GrowthConsumer
open CompanionTheory.PlacePermOperatorBicommutantSpan

/-- A finite-place lower estimate with one positive coefficient at arbitrarily large
natural dilations. Its result refers to the same original inputBox used in the integral. -/
abbrev RankOneGrowthProvider : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) →
  ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 →
             Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M)
                                        (coordHerm (Fv F v) σ b (lam v) 1) (m v)) →
  ∀ β : F, β ≠ 0 → (∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧
      κ * (a : ℝ)^(Module.finrank ℚ F * (2*M-2)) ≤ finiteProduct σ b m β a

/-- The pinned rank-one conclusion with the finite-place witness supplier exposed. -/
abbrev RankOneConclusion : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
  ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → SWMeas σ J T hT

set_option maxHeartbeats 800000 in
/-- The two branches from the pinned SwOne source, with the growth dependency made
explicit and the nonzero scalar comparison discharged by original_scalar_comparison.
The proof uses the Euler and theta integral theorems directly. -/
theorem sw_one_of_growth (provider : RankOneGrowthProvider) : RankOneConclusion := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨t1, t2⟩ := theta_inv F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 T
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_isEulerProd_of_invariant_of_fiber_supported F E σ hcm M J hJ 1 (Or.inr hM) T hT hd d b li lam hli hlam mi hmi m hm _
    (theta_measure_locally_finite F E σ hcm M J hJ hM μ 𝓕 hμ h𝓕 T hT hd) t1 t2
  by_cases h0 : mi (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 M _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 M 0 1 _ _).2.2 hc.1 hc.2.1 h0
  suffices h : c = 1 from h ▸ hc
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  simp only [he] at hc h0
  push Not at h0
  obtain ⟨φ, C, φc, φp, φf, hb⟩ := GlobalTheory.T.thetaMeas_rank_one_sub_density_product_le F E σ hcm M J hJ hM d b li lam hli hlam μ 𝓕 hμ h𝓕 mi hmi m hm β (hβ hd)
  obtain ⟨κ, hκ, hg⟩ := provider F E σ hcm M J hJ hM d b lam hlam m hm β (hβ hd) h0.2
  have : BorelSpace (Fin 1 → Fin M → Ainf F ⊗[F] E) := by
    have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 M
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) := φc.measurable.ennreal_ofReal
  refine (original_scalar_comparison σ J b μ 𝓕 mi m β φ hM hc h0.1 hφm φp φf
    hκ hg hb (fun a ha0 => ?_)).1
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0.ne'
  have hA : ∀ v, MeasurableSet {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} ∧
      m v (hermScal (Fv F v) σ (algebraMap F _ β))
        {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤ := fun v => by
    have hR := GlobalTheory.T.completion_is_local_ring F v
    have hR' := hR
    obtain ⟨_, _, _, _, -⟩ := hR'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 M
    have hu : IsUnit (a : Fv F v ⊗[F] E) := by simpa using (Ne.isUnit haE).map (inclR (F := F) (Fv F v))
    have hK : IsCompact {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} :=
      (Homeomorph.smul hu.unit).isCompact_preimage.2 ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 M).2.2.2.1 v).1
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm M J hJ (Fv F v) hR 1 _ _ _ (k1 1 M) (k2 1) (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β))).1
    exact ⟨hK.measurableSet, hK.measure_lt_top⟩
  obtain ⟨-, e3⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 M _ c _ _ hc _ _ hφm (fun v => (hA v).1) (fun v => (hA v).2)
    (((GlobalTheory.T.lattice_stable_almost_everywhere F E σ hcm d b 1 M).1 (Matrix.of fun _ _ => (a : E)) ((Matrix.det_unique _).trans_ne haE)).mono fun v hv => Set.ext fun X => by
      refine Iff.trans (Iff.of_eq (congrArg (· ∈ latV b v) (funext fun p => funext fun i => ?_))) (hv X)
      rw [Subsingleton.elim p 0]
      simp [rmul, mul_comm])
  exact e3

end GrowthConsumer
#print axioms GrowthConsumer.sw_one_of_growth
