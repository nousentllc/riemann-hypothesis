import RamField
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace RamField

/-- The coordinate inclusion of integral pairs is an open embedding of the full lattice. -/
def pairInc (p : ℤ_[2] × ℤ_[2]) : K :=
  coordinates.symm ((p.1 : ℚ_[2]), (p.2 : ℚ_[2]))

theorem pairInc_openEmbedding : IsOpenEmbedding pairInc :=
  coordinates.toHomeomorph.symm.isOpenEmbedding.comp
    (PadicInt.isOpenEmbedding_coe.prodMap PadicInt.isOpenEmbedding_coe)

theorem integers_eq : integers = pairInc '' Set.univ := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨(y.re, y.im),Set.mem_univ _,rfl⟩
  · rintro ⟨⟨a,b⟩,_,rfl⟩
    exact ⟨⟨a,b⟩,rfl⟩

theorem integers_compact : IsCompact integers := by
  rw [integers_eq]
  exact isCompact_univ.image pairInc_openEmbedding.continuous

theorem integers_open : IsOpen integers := by
  rw [integers_eq]
  exact pairInc_openEmbedding.isOpenMap _ isOpen_univ

private def component (k : ℕ) (a : ZMod (2^k)) : Set ℤ_[2] := {x | TargetOne.digit k x=a}

private theorem component_eq (k : ℕ) (a : ZMod (2^k)) :
    component k a = Metric.closedBall (a.val : ℤ_[2]) ((2:ℝ)^(-(k:ℤ))) := by
  rw [← TargetOne.ball_digit, TargetOne.digit_nat]
  rfl

private theorem cylinder_as_product (k : ℕ) (b : R k) :
    cylinder k b = pairInc '' (component k b.re ×ˢ component k b.im) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change digit k y = b at hy
    exact ⟨(y.re,y.im),⟨congrArg QuadraticAlgebra.re hy,congrArg QuadraticAlgebra.im hy⟩,rfl⟩
  · rintro ⟨⟨a,c⟩,⟨ha,hc⟩,rfl⟩
    exact ⟨⟨a,c⟩, QuadraticAlgebra.ext ha hc,rfl⟩

theorem compact_cylinder (k : ℕ) (b : R k) : IsCompact (cylinder k b) := by
  rw [cylinder_as_product,component_eq,component_eq]
  exact (Metric.isClosed_closedBall.isCompact.prod Metric.isClosed_closedBall.isCompact).image
    pairInc_openEmbedding.continuous

theorem open_cylinder (k : ℕ) (b : R k) : IsOpen (cylinder k b) := by
  rw [cylinder_as_product,component_eq,component_eq]
  apply pairInc_openEmbedding.isOpenMap
  exact (IsUltrametricDist.isOpen_closedBall _ (by positivity)).prod
    (IsUltrametricDist.isOpen_closedBall _ (by positivity))

theorem disjoint_cyl (k : ℕ) : Pairwise (fun a b => Disjoint (cylinder k a) (cylinder k b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,h⟩
  exact hab (hx.symm.trans ((inc_injective h) ▸ hy))

theorem union_cyl (k : ℕ) : ⋃ b, cylinder k b = integers := by
  ext x
  constructor
  · rintro ⟨_,⟨b,rfl⟩,y,_,rfl⟩
    exact ⟨y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact Set.mem_iUnion.mpr ⟨digit k y,y,rfl,rfl⟩

theorem cyl_mass (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (k : ℕ) (b : R k) : lam (cylinder k b)=1/(2^k : ℝ≥0∞)^2 := by
  classical
  let e := QuadraticAlgebra.equivProd (2:ZMod (2^k)) 0
  let : Fintype (R k) := Fintype.ofEquiv _ e.symm
  have hc : Fintype.card (R k) = (2^k)^2 := by
    rw [Fintype.card_congr e,Fintype.card_prod,ZMod.card,pow_two]
  have meas (t : R k) : MeasurableSet (cylinder k t) := (open_cylinder k t).measurableSet
  have flat (t : R k) : lam (cylinder k t)=lam (cylinder k b) := by
    obtain ⟨z,hz⟩ := digit_surjective k (b-t)
    have pre : (fun x : K => inc z + x) ⁻¹' cylinder k b = cylinder k t := by
      ext x
      constructor
      · rintro ⟨y,hy,h⟩
        refine ⟨y-z,?_,?_⟩
        · change digit k (y-z) = t
          rw [map_sub,show digit k y=b from hy,hz]; ring
        · rw [map_sub,h]; exact add_sub_cancel_left _ _
      · rintro ⟨y,hy,rfl⟩
        refine ⟨z+y,?_,map_add ..⟩
        change digit k (z+y)=b
        rw [map_add,hz,show digit k y=t from hy]; ring
    rw [← pre,measure_preimage_add]
  have h := measure_iUnion (μ := lam) (disjoint_cyl k) meas
  rw [union_cyl,hvol,tsum_fintype,Finset.sum_congr rfl (fun t _ => flat t)] at h
  simp only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at h
  exact (ENNReal.eq_div_iff (by positivity) (by finiteness)).mpr h.symm

theorem small_four (N : Set K) (hN : N ∈ 𝓝 (4:K)) :
    ∃ k : ℕ, cylinder (k+5) 4 ⊆ N := by
  have pre : pairInc ⁻¹' N ∈ 𝓝 ((4,0) : ℤ_[2] × ℤ_[2]) :=
    pairInc_openEmbedding.continuous.continuousAt (by exact hN)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp pre
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹ < 1)
  have hr : (2:ℝ)^(-((k+5:ℕ):ℤ)) < ε := by
    rw [zpow_neg,zpow_natCast,←inv_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : k≤k+5)) hk
  refine ⟨k,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  change digit (k+5) y = 4 at hy
  have h1 : TargetOne.digit (k+5) y.re = TargetOne.digit (k+5) 4 := by
    rw [map_ofNat]; exact congrArg QuadraticAlgebra.re hy
  have h2 : TargetOne.digit (k+5) y.im = TargetOne.digit (k+5) 0 := by
    rw [map_zero]; exact congrArg QuadraticAlgebra.im hy
  have hb1 : y.re ∈ Metric.closedBall (4 : ℤ_[2]) ((2:ℝ)^(-((k+5:ℕ):ℤ))) := by
    rw [← TargetOne.ball_digit]; exact h1
  have hb2 : y.im ∈ Metric.closedBall (0 : ℤ_[2]) ((2:ℝ)^(-((k+5:ℕ):ℤ))) := by
    rw [← TargetOne.ball_digit]; exact h2
  apply hball (a := (y.re,y.im))
  exact max_lt ((Metric.mem_closedBall.mp hb1).trans_lt hr)
    ((Metric.mem_closedBall.mp hb2).trans_lt hr)

theorem standard_exists : ∃ lam : Measure K, lam.IsAddHaarMeasure ∧ lam integers = 1 := by
  let C : TopologicalSpace.PositiveCompacts K := ⟨⟨integers,integers_compact⟩, by
    change (interior integers).Nonempty
    rw [integers_open.interior_eq]
    exact ⟨inc 0,0,rfl⟩⟩
  exact ⟨Measure.addHaarMeasure C,inferInstance,Measure.addHaarMeasure_self⟩

end RamField
#print axioms RamField.cyl_mass
#print axioms RamField.small_four
#print axioms RamField.standard_exists
