import OverlapMeasure
import OverlapVolume

open MeasureTheory Topology Set
open scoped ENNReal NNReal
noncomputable section
namespace PivotOverlap
open RamField FourChart

def coords : Fin 5 → Set K := Fin.cons (cell 5 (8/5)) (fun _ => cell 5 0)
def transverseBox : Set W := univ.pi coords
def transverseHaar (lam : Measure K) := Measure.pi (fun _ : Fin 5 => lam)

theorem transverse_meas : MeasurableSet transverseBox := by
  apply MeasurableSet.univ_pi
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i <;> exact (cell_closed ..).measurableSet

theorem transverse_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    transverseHaar lam transverseBox = (1/4:ℝ≥0∞)^25 := by
  rw [transverseHaar,transverseBox,Measure.pi_pi]
  simp [coords,Fin.prod_univ_succ,cell_volume lam hvol]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat]

theorem decode_transverse {w : W} (hw : w∈transverseBox) :
    ∃ (v : D) (z : Z), ∀ u, (point u v z).2=w := by
  have hv : w 0 ∈ cell 5 (8/5) := hw 0 (mem_univ _)
  rw [affine_cell] at hv
  obtain ⟨v,_,hv⟩ := hv
  have hz (j : Fin 4) : ∃ a : D, 32*a.val/5 = w j.succ := by
    have h : w j.succ ∈ cell 5 0 := hw j.succ (mem_univ _)
    rw [show (0:K)=0/5 by ring,affine_cell] at h
    obtain ⟨a,_,h⟩ := h
    exact ⟨a,by norm_num at h ⊢; exact h⟩
  choose z hz using hz
  refine ⟨v,z,fun u => funext (fun i => Fin.cases ?_ (fun j => ?_) i)⟩
  · norm_num [point] at hv ⊢; exact hv
  · exact hz j

theorem overlap_subset : transverseBox ⊆ transverse 3 0 := by
  intro w hw
  obtain ⟨v,z,h⟩ := decode_transverse hw
  rw [←h 0]; exact (patch_inside 0 v z).2

theorem first_subset : cell 7 (-6/5:K) ⊆ cell 3 2 := by
  have h := (patch_inside 0 0 (0:Z)).1
  have hc : (-6/5:K) ∈ cell 3 2 := by simpa [point] using h
  exact fun _ hx => nest (by decide : 3 ≤ 7) hc hx

theorem overlap_root (t : D) (w : W) (hw : w∈transverseBox) :
    ∃ x ∈ cell 7 (-6/5:K), gram x w=label t := by
  obtain ⟨v,z,h⟩ := decode_transverse hw
  let u := swapX t z v
  refine ⟨(point u v z).1,?_,?_⟩
  · rw [affine_cell]; exact ⟨u,mem_univ _,by norm_num [point]⟩
  · rw [←h u,←original_gram]
    exact graph_gram t (z,v)

theorem physical_slabs (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (t : D) (r : ℕ) (hr : 7 ≤ r) :
    ((transverseHaar lam).prod lam) (slab transverseBox 7 (-6/5) r (label t)) =
      (1/4:ℝ≥0∞)^25 * (1/(2^r:ℝ≥0∞)^2) := by
  rw [slab_mass lam hvol _ transverse_meas hr first_subset (overlap_root t),transverse_mass lam hvol]

theorem old_root_in_overlap (w : FourChart.TBox) (hw : w.val∈transverseBox) :
    (FourChart.point 0 w).2 ∈ cell 7 (-6/5) := by
  obtain ⟨x,hx,he⟩ := overlap_root 0 w.val hw
  have hold := graph_support 0 w
  have hsq : (FourChart.point 0 w).2^2=x^2 := by
    change (FourChart.point 0 w).2^2 + ∑ j, w.val j ^ 2 = _ at hold
    change x^2 + ∑ j, w.val j ^ 2 = _ at he
    have h4 : label 0=4 := center.1
    rw [h4] at he
    have hs : scalarTarget 0=4 := by simp [scalarTarget]
    rw [hs] at hold
    linear_combination hold-he
  have hy : (FourChart.point 0 w).2∈cell 3 2 := root_box 0 (decode w)
  have hn := delta_norm hy (first_subset hx)
  rw [hsq,sub_self,norm_zero] at hn
  have hzero : ‖(FourChart.point 0 w).2-x‖=0 := by linarith
  rwa [sub_eq_zero.mp (norm_eq_zero.mp hzero)]

theorem previous_test (lam : Measure K)
    (factor : ℝ≥0∞) {S : Set W} (hS : MeasurableSet S) (hsub : S ⊆ transverseBox) :
    chartMeasure factor (transverseHaar lam) 0 (S ×ˢ cell 7 (-6/5)) =
      factor*transverseHaar lam S := by
  have hpre : FourChart.point 0 ⁻¹' (S ×ˢ cell 7 (-6/5)) =
      FourChart.point 0 ⁻¹' (S ×ˢ cell 3 2) := by
    ext w
    constructor
    · intro h; exact ⟨h.1,first_subset h.2⟩
    · intro h; exact ⟨h.1,old_root_in_overlap w (hsub h.1)⟩
  have eq : chartMeasure factor (transverseHaar lam) 0 (S ×ˢ cell 7 (-6/5)) =
      chartMeasure factor (transverseHaar lam) 0 (S ×ˢ cell 3 2) := by
    simp only [chartMeasure,Measure.smul_apply,Measure.map_apply (point_continuous _).measurable
      (hS.prod (cell_closed ..).measurableSet),hpre]
  rw [eq,measured_box _ _ hS (hsub.trans overlap_subset) (by decide)]

theorem previous_chart (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (factor : ℝ≥0∞) :
    chartMeasure factor (transverseHaar lam) 0 (transverseBox ×ˢ cell 7 (-6/5)) =
      factor*(1/4:ℝ≥0∞)^25 := by
  rw [previous_test lam factor transverse_meas (fun _ h => h),transverse_mass lam hvol]

end PivotOverlap
#print axioms PivotOverlap.decode_transverse
#print axioms PivotOverlap.physical_slabs
#print axioms PivotOverlap.old_root_in_overlap
#print axioms PivotOverlap.previous_chart
#print axioms PivotOverlap.previous_test
