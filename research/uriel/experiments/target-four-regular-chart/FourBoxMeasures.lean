import FourChart

open MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal NNReal
noncomputable section
namespace FourChart
open RamField

def integralHaar (lam : Measure K) : Measure D := lam.comap ((↑) : D → K)

private theorem embedD : MeasurableEmbedding ((↑) : D → K) :=
  MeasurableEmbedding.subtype_coe integers_open.measurableSet

theorem integral_univ (lam : Measure K) (hvol : lam integers=1) : integralHaar lam univ=1 := by
  rw [integralHaar,embedD.comap_apply,Set.image_univ,Subtype.range_val_subtype]
  exact hvol

def disc (n : ℕ) (a : D) := Metric.closedBall a ((1/2:ℝ)^n)

theorem disc_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) (n : ℕ) (a : D) :
    integralHaar lam (disc n a) = 1/(2^n:ℝ≥0∞)^2 := by
  have ha : a.val ∈ cell 0 0 := by
    simpa [cell] using (mem_D a.val).mp a.2
  have hsub : cell n a.val ⊆ integers := by
    intro x hx
    have h := nest (Nat.zero_le n) ha hx
    simpa [cell,mem_D] using h
  change integralHaar lam (((↑) : D → K) ⁻¹' cell n a.val) = _
  rw [integralHaar,embedD.comap_preimage,Subtype.range_val_subtype]
  change lam (cell n a.val ∩ integers) = _
  rw [inter_eq_left.mpr hsub,cell_volume lam hvol]

def discs : Set (Set D) := {U | ∃ n a, U=disc n a}

theorem disc_basis : TopologicalSpace.IsTopologicalBasis discs := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨n,a,rfl⟩
    exact IsUltrametricDist.isOpen_closedBall a (by positivity)
  · intro a U ha ho
    obtain ⟨e,he,h⟩ := Metric.isOpen_iff.mp ho a ha
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one he (by norm_num : (1/2:ℝ)<1)
    exact ⟨disc n a,⟨n,a,rfl⟩,Metric.mem_closedBall_self (by positivity),
      (Metric.closedBall_subset_ball hn).trans h⟩

theorem disc_pi : IsPiSystem discs := by
  rintro _ ⟨n,a,rfl⟩ _ ⟨m,b,rfl⟩ h
  rcases IsUltrametricDist.closedBall_subset_trichotomy (x:=a) (y:=b)
    (r:=(1/2:ℝ)^n) (s:=(1/2:ℝ)^m) with hab|hba|hd
  · exact ⟨n,a,inter_eq_left.mpr hab⟩
  · exact ⟨m,b,inter_eq_right.mpr hba⟩
  · exact False.elim ((Set.disjoint_iff_inter_eq_empty.mp hd ▸ h).ne_empty rfl)

theorem iso_preserves (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) (e : D ≃ᵢ D) :
    MeasurePreserving e (integralHaar lam) (integralHaar lam) := by
  have hp : IsProbabilityMeasure (integralHaar lam) := ⟨integral_univ lam hvol⟩
  let : IsProbabilityMeasure (integralHaar lam) := hp
  let mu := integralHaar lam
  have hmap := Measure.isProbabilityMeasure_map (μ:=mu) e.continuous.aemeasurable
  refine ⟨e.continuous.measurable, ext_of_generate_finite discs
    ((BorelSpace.measurable_eq (α:=D)).trans disc_basis.borel_eq_generateFrom) disc_pi ?_ ?_⟩
  · rintro _ ⟨n,a,rfl⟩
    rw [Measure.map_apply e.continuous.measurable (show MeasurableSet (disc n a) from Metric.isClosed_closedBall.measurableSet)]
    have h : e ⁻¹' disc n a = disc n (e.symm a) := by
      ext x
      change dist (e x) a ≤ _ ↔ dist x (e.symm a) ≤ _
      rw [←e.dist_eq x (e.symm a),e.apply_symm_apply]
    rw [h,disc_mass lam hvol,disc_mass lam hvol]
  · simp [Measure.map_apply_of_aemeasurable e.continuous.aemeasurable]

def translateIso (b : D) : D ≃ᵢ D where
  toFun x := x+b
  invFun x := x-b
  left_inv _ := add_sub_cancel_right _ _
  right_inv _ := sub_add_cancel _ _
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_add_right _ _ _

/-- Full Borel change of variables on the local normalized chart. The transverse
measure can be restricted arbitrarily, including to any measurable vector box. -/
theorem normalized_preserves (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1)
    (kap : Measure WD) [SFinite kap] :
    MeasurePreserving normalized ((integralHaar lam).prod kap) ((integralHaar lam).prod kap) := by
  let mu := integralHaar lam
  let : IsProbabilityMeasure mu := ⟨integral_univ lam hvol⟩
  have hg (w : WD) : MeasurePreserving (fun x : D => pivot x+offset w) mu mu :=
    (iso_preserves lam hvol (pivotEquiv.trans (translateIso (offset w))))
  have hm : Measurable (Function.uncurry (fun (w : WD) (x : D) => pivot x+offset w)) := by
    have hp := pivot_isometry.continuous
    unfold Function.uncurry offset
    fun_prop
  have h := (MeasurePreserving.id kap).skew_product (g:=fun w x => pivot x+offset w) hm
    (Filter.Eventually.of_forall fun w => (hg w).map_eq)
  exact (Measure.measurePreserving_swap (μ:=kap) (ν:=mu)).comp (h.comp (Measure.measurePreserving_swap (μ:=mu) (ν:=kap)))

abbrev TBox := (transverse 3 (0:W))
def decode (w : TBox) (j : Fin 5) : D :=
  ⟨w.val j/8,(mem_D _).mpr <| by
    have hj : w.val j ∈ cell 3 0 := w.2 j (mem_univ _)
    change ‖w.val j-0‖ ≤ _ at hj
    rw [sub_zero] at hj
    rw [norm_div,show (8:K)=2^3 by norm_num,norm_scale,div_le_one₀ (by positivity)]
    exact hj⟩

def point (t : D) (w : TBox) : W × K := (w.val,(graph t (decode w)).1)

set_option maxHeartbeats 600000 in
theorem point_continuous (t : D) : Continuous (point t) := by
  have hd : Continuous (fun w : TBox => decode w) := by
    apply continuous_pi; intro i
    apply Continuous.subtype_mk
    exact ((continuous_apply i).comp continuous_subtype_val).div_const _
  have hp : Continuous (fun w : TBox => (t,decode w)) := continuous_const.prodMk hd
  have hg := Continuous.comp (f := fun w : TBox => (t,decode w)) graph_continuous hp
  exact continuous_subtype_val.prodMk hg.fst

def chartMeasure (factor : ℝ≥0∞) (kap : Measure W) (t : D) : Measure (W × K) :=
  factor • (kap.comap ((↑) : TBox → W)).map (point t)

theorem graph_support (t : D) (w : TBox) :
    gram (point t w).2 (point t w).1=scalarTarget t := by
  have h (j : Fin 5) : 8*(decode w j).val = w.val j := by change 8*(w.val j/8)=_; ring
  simpa [point,h] using root_formula t (decode w)

theorem factor_two (kap : Measure W) (t : D) :
    chartMeasure 16 kap t = (2:ℝ≥0∞) • chartMeasure 8 kap t := by
  unfold chartMeasure; rw [smul_smul]; norm_num

theorem measured_box (c : ℝ≥0∞) (kap : Measure W) {S : Set W} (hS : MeasurableSet S)
    (hsub : S ⊆ transverse 3 0) {m : ℕ} (hm : m ≤ 4) :
    chartMeasure c kap 0 (S ×ˢ cell m 2) = c*kap S := by
  have emb : MeasurableEmbedding ((↑) : TBox → W) :=
    MeasurableEmbedding.subtype_coe (transverse_closed _ _).measurableSet
  have hp : point 0 ⁻¹' (S ×ˢ cell m 2) = ((↑) : TBox → W) ⁻¹' S := by
    ext w
    exact and_iff_left (cell_mono hm 2 (root_child (decode w)))
  rw [chartMeasure,Measure.smul_apply,Measure.map_apply (point_continuous _).measurable
    (hS.prod (cell_closed ..).measurableSet),hp,emb.comap_preimage,Subtype.range_val_subtype,smul_eq_mul]
  change c*kap (S ∩ transverse 3 0) = _
  rw [inter_eq_left.mpr hsub]

end FourChart
#print axioms FourChart.iso_preserves
#print axioms FourChart.normalized_preserves
#print axioms FourChart.graph_support
#print axioms FourChart.factor_two
#print axioms FourChart.measured_box
