import Mathlib
noncomputable section
open scoped NNReal
open MeasureTheory Filter Topology
namespace UpperTheory.TP
private theorem abs_tail_pk {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this

#print axioms abs_tail_pk
end UpperTheory.TP
end
