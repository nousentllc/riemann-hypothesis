import PivotOverlap

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart

abbrev P := Z × D
def changeX (t : D) (p : P) : P := (p.1,swapX t p.1 p.2)
def changeY (t : D) (p : P) : P := (p.1,swapY t p.1 p.2)
def xGraph (t : D) (p : P) := point (swapX t p.1 p.2) p.2 p.1
def yGraph (t : D) (p : P) := point p.2 (swapY t p.1 p.2) p.1

theorem contC : Continuous C := by unfold C; fun_prop
theorem cont_changeX (t : D) : Continuous (changeX t) := by
  have ha := A.symm.continuous
  have hb := B.continuous
  have h := contC
  unfold changeX swapX
  fun_prop

theorem cont_changeY (t : D) : Continuous (changeY t) := by
  have ha := A.continuous
  have hb := B.symm.continuous
  have h := contC
  unfold changeY swapY
  fun_prop

def overlapHomeo (t : D) : P ≃ₜ P where
  toFun := changeX t
  invFun := changeY t
  left_inv p := Prod.ext rfl (inverseX t p.1 p.2)
  right_inv p := Prod.ext rfl (inverseY t p.1 p.2)
  continuous_toFun := cont_changeX t
  continuous_invFun := cont_changeY t

theorem charts_match (t : D) : yGraph t ∘ changeX t = xGraph t := by
  funext p
  simp [changeX,xGraph,yGraph,inverseX]

theorem graph_gram (t : D) (p : P) :
    TargetOne.Q (six (xGraph t p).1 (xGraph t p).2)=label t := by
  rw [xGraph,gram_point,(solve ..).mpr rfl]

theorem cont_point : Continuous (fun q : (D × D) × Z => point q.1.1 q.1.2 q.2) := by
  apply Continuous.prodMk
  · change Continuous (fun q : (D × D) × Z => (-6+128*q.1.1.val)/5); fun_prop
  · apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun q : (D × D) × Z => (8+32*q.1.2.val)/5); fun_prop
    · change Continuous (fun q : (D × D) × Z => 32*(q.2 j).val/5); fun_prop

set_option maxHeartbeats 800000 in
theorem cont_yGraph (t : D) : Continuous (yGraph t) := by
  have hy : Continuous (fun p : P => (changeY t p).2) := continuous_snd.comp (cont_changeY t)
  have hm : Continuous (fun p : P => ((p.2,(changeY t p).2),p.1)) :=
    ((continuous_snd (X:=Z) (Y:=D)).prodMk hy).prodMk continuous_fst
  exact Continuous.comp (f:=fun p : P => ((p.2,(changeY t p).2),p.1)) cont_point hm

theorem normalized_glue (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (nu : Measure Z) [SFinite nu] (t : D) :
    MeasurePreserving (changeX t) (nu.prod (integralHaar lam)) (nu.prod (integralHaar lam)) := by
  let : IsProbabilityMeasure (integralHaar lam) := ⟨integral_univ lam hvol⟩
  apply (MeasurePreserving.id nu).skew_product (g:=fun z v => swapX t z v)
  · exact (continuous_snd.comp (cont_changeX t)).measurable
  · exact Filter.Eventually.of_forall (fun z => (iso_preserves lam hvol (transition t z)).map_eq)

theorem graph_measure_eq (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (nu : Measure Z) [SFinite nu] (t : D) :
    (nu.prod (integralHaar lam)).map (xGraph t) = (nu.prod (integralHaar lam)).map (yGraph t) := by
  rw [← charts_match,←Measure.map_map (cont_yGraph t).measurable (cont_changeX t).measurable,
    (normalized_glue lam hvol nu t).map_eq]

theorem scalar_weights :
    (16:ℝ≥0∞)*(1/4)^25 = 1/2^46 ∧ (256:ℝ≥0∞)*(1/4)^27 = 1/2^46 := by
  constructor <;> apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat]

theorem physical_glue (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (nu : Measure Z) [SFinite nu] (t : D) :
    (16*(1/4)^25 : ℝ≥0∞) • (nu.prod (integralHaar lam)).map (xGraph t) =
    (256*(1/4)^27 : ℝ≥0∞) • (nu.prod (integralHaar lam)).map (yGraph t) := by
  rw [scalar_weights.1,scalar_weights.2,graph_measure_eq lam hvol nu t]

theorem total_masses (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (nu : Measure Z) [IsProbabilityMeasure nu] (t : D) :
    let mu := (nu.prod (integralHaar lam)).map (yGraph t)
    ((1/2^46 : ℝ≥0∞) • mu) univ = 1/2^46 ∧ ((1/2^47 : ℝ≥0∞) • mu) univ = 1/2^47 := by
  let : IsProbabilityMeasure (integralHaar lam) := ⟨integral_univ lam hvol⟩
  let := Measure.isProbabilityMeasure_map (μ:=nu.prod (integralHaar lam)) (cont_yGraph t).aemeasurable
  simp [Measure.smul_apply,smul_eq_mul]

end PivotOverlap
#print axioms PivotOverlap.overlapHomeo
#print axioms PivotOverlap.graph_gram
#print axioms PivotOverlap.normalized_glue
#print axioms PivotOverlap.graph_measure_eq
#print axioms PivotOverlap.physical_glue
#print axioms PivotOverlap.total_masses
