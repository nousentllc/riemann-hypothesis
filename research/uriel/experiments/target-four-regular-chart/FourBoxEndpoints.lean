import FourBoxMeasures

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace FourChart
open RamField

theorem parent_sub {m : ℕ} (hm : 3 ≤ m) :
    transverse m 0 ⊆ transverse 3 0 :=
  fun _ hw j hj => cell_mono hm 0 (hw j hj)

theorem box_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (m : ℕ) (hm : 3 ≤ m) (hm' : m ≤ 4) (c : ℝ≥0∞) :
    chartMeasure c (Measure.pi fun _ : Fin 5 => lam) 0 (transverse m 0 ×ˢ cell m 2) =
      c*(1/(2^m:ℝ≥0∞)^2)^5 := by
  rw [measured_box _ _ (transverse_closed ..).measurableSet (parent_sub hm) hm',
    transverse_volume lam hvol]

theorem negative_child : Disjoint (cell 4 (2:K)) (cell 4 10) := by
  apply Set.disjoint_left.mpr; intro x hx hy
  have hx' : (2:K) ∈ cell 4 x := by
    change ‖(2:K)-x‖ ≤ _
    rw [norm_sub_rev]; exact hx
  have h := nest (le_refl 4) hy hx'
  change ‖(2:K)-10‖ ≤ _ at h
  rw [show (2:K)-10= -(2^3) by norm_num,norm_neg,norm_scale] at h
  norm_num at h

theorem missing_mass (c : ℝ≥0∞) (kap : Measure W) {S : Set W} (hs : MeasurableSet S) :
    chartMeasure c kap 0 (S ×ˢ cell 4 10) = 0 := by
  have he : point 0 ⁻¹' (S ×ˢ cell 4 10) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact Set.disjoint_left.mp negative_child (root_child (decode w)) hw.2
  rw [chartMeasure,Measure.smul_apply,Measure.map_apply (point_continuous _).measurable
    (hs.prod (cell_closed ..).measurableSet),he,measure_empty,smul_zero]

theorem exact_boxes (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let kap := Measure.pi fun _ : Fin 5 => lam
    chartMeasure 16 kap 0 (transverse 3 0 ×ˢ cell 3 2) = 1/2^26 ∧
    chartMeasure 8 kap 0 (transverse 3 0 ×ˢ cell 3 2) = 1/2^27 ∧
    chartMeasure 16 kap 0 (transverse 4 0 ×ˢ cell 4 2) = 1/2^36 ∧
    chartMeasure 8 kap 0 (transverse 4 0 ×ˢ cell 4 2) = 1/2^37 := by
  dsimp only
  simp only [box_mass lam hvol 3 (by decide) (by decide),box_mass lam hvol 4 (by decide) (by decide)]
  repeat' constructor
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat]

theorem target_slab_law (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (kap : Measure W) {S : Set W} (hs : MeasurableSet S) (hsub : S ⊆ transverse 3 0)
    (m r : ℕ) (hm : 3 ≤ m) (hm' : m ≤ 4) (hr : m ≤ r) :
    (kap.prod lam) (slab S m 2 r 4) =
    chartMeasure 8 kap 0 (S ×ˢ cell m 2) * ((2:ℝ≥0∞) • lam) (cell (r+2) 4) := by
  rw [centered_slabs lam hvol kap hs hsub hm hm' hr,measured_box _ _ hs hsub hm',
    Measure.smul_apply,smul_eq_mul,cell_volume lam hvol]
  have h : (1/(2^r:ℝ≥0∞)^2) = 8*(2*(1/(2^(r+2):ℝ≥0∞)^2)) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_one,ENNReal.toReal_ofNat,
      ENNReal.toReal_pow,pow_add]
    ring
  rw [h]; ac_rfl

theorem nearby_slabs (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (kap : Measure W) {S : Set W} (hs : MeasurableSet S) (hsub : S ⊆ transverse 3 0)
    (t : D) (r : ℕ) (hr : 3 ≤ r) :
    (kap.prod lam) (slab S 3 2 r (scalarTarget t)) = kap S * (1/(2^r:ℝ≥0∞)^2) := by
  apply slab_mass lam hvol kap hs hr (fun _ h => h)
  intro w hw
  obtain ⟨z,hz⟩ := physical_transverse (hsub hw)
  refine ⟨(graph t z).1,root_box t z,?_⟩
  rw [show w = _ from funext hz,root_formula]

theorem sqrt_minus_seven : ∃ c : D, c^2 = -7 := by
  obtain ⟨u,hu⟩ := pivot_surjective (-1)
  refine ⟨1+4*u,?_⟩
  change u+2*u^2 = -1 at hu
  linear_combination 8*hu

end FourChart
#print axioms FourChart.exact_boxes
#print axioms FourChart.target_slab_law
#print axioms FourChart.nearby_slabs
#print axioms FourChart.missing_mass
#print axioms FourChart.sqrt_minus_seven
