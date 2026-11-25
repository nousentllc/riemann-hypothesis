import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqSmul
open Set MeasureTheory Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace HaarSlices

/-- Computing both iterated integrals bounds the original tube. Each
translation preserves source mass. The parameter has probability one. -/
theorem average {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [IsProbabilityMeasure ν]
    (T W : Set X) (hT : MeasurableSet T) (hW : MeasurableSet W)
    (move : X × Y → X) (hm : Measurable move)
    (hpres : ∀ y, MeasurePreserving (fun x => move (x,y)) μ μ)
    (a : ℝ≥0∞) (hlow : ∀ x ∈ W, a ≤ ν {y | move (x,y) ∈ T}) :
    μ W * a ≤ μ T := by
  let S := move ⁻¹' T
  have hs : MeasurableSet S := hT.preimage hm
  calc
    μ W * a = ∫⁻ x, W.indicator (fun _ => a) x ∂μ := by
      rw [lintegral_indicator hW, setLIntegral_const, mul_comm]
    _ ≤ (μ.prod ν) S := by
      rw [Measure.prod_apply hs]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ W
      · rw [Set.indicator_of_mem hx]; exact hlow x hx
      · simp [Set.indicator_of_notMem hx]
    _ = μ T := by
      rw [Measure.prod_apply_symm hs]
      have hsec (y : Y) : μ (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S)) = μ T := by
        exact (hpres y).measure_preimage hT.nullMeasurableSet
      simpa [S, Function.comp_def, Set.preimage, hsec] using
        (show (∫⁻ y, μ {x | move (x,y) ∈ T} ∂ν) = μ T from by
          have e (y:Y) : μ {x | move (x,y) ∈ T} = μ T :=
            (hpres y).measure_preimage hT.nullMeasurableSet
          simp_rw [e]; simp)

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- An affine Haar calibration on a single test ball gives the constant
for every smaller target. Only the ball and its preimage need normalizing. -/
theorem affine_slice (lam : Measure K) [lam.IsAddHaarMeasure] (u : Kˣ) (b : K)
    (O D : Set K) (hO : MeasurableSet O) (hD : MeasurableSet D)
    (hvol : lam O = 1) (hpre : (fun y : K => (u:K)*y+b) ⁻¹' D = O)
    {V : Set K} (hV : MeasurableSet V) (hVD : V ⊆ D) :
    (lam.restrict O) ((fun y : K => (u:K)*y+b) ⁻¹' V) = (lam D)⁻¹ * lam V := by
  let f := fun y : K => (u:K)*y+b
  have hm : Measurable f := (continuous_const.mul continuous_id |>.add continuous_const).measurable
  let c := ((distribHaarChar K u)⁻¹ : ℝ≥0)
  have eqv (T : Set K) (hT : MeasurableSet T) : lam (f ⁻¹' T) = (c:ℝ≥0∞) * lam T := by
    change lam ((fun y : K => (u:K)*y) ⁻¹' ((fun y : K => y+b) ⁻¹' T)) = _
    have hm₁ : Measurable (fun y : K => (u:K)*y) := (continuous_const.mul continuous_id).measurable
    have hm₂ : Measurable (fun y : K => y+b) := measurable_id.add measurable_const
    rw [← Measure.map_apply hm₁ (hT.preimage hm₂),
        GlobalTheory.CompanionTheory.SW.ModDet.map_mul_unit, Measure.smul_apply,
        (measurePreserving_add_right lam b).measure_preimage hT.nullMeasurableSet]
    rfl
  have he := eqv D hD
  change lam ((fun y : K => (u:K)*y+b) ⁻¹' D) = _ at he
  rw [hpre, hvol] at he
  have hc : (c:ℝ≥0∞) = (lam D)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left he.symm
  have sub : f ⁻¹' V ⊆ O := by rw [← hpre]; exact preimage_mono hVD
  change (lam.restrict O) (f ⁻¹' V) = _
  rw [Measure.restrict_apply (hV.preimage hm), inter_eq_self_of_subset_left sub, eqv V hV, hc]
end HaarSlices
#print axioms HaarSlices.average
#print axioms HaarSlices.affine_slice
