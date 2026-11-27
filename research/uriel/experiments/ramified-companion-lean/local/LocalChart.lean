import Mathlib

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace LocalChart

/-- An affine unit pivot has one solution above each target and transverse
parameter, over every commutative ring including dyadic quotients. -/
def graphEquiv {R W : Type*} [CommRing R] (u : W → Rˣ) (q : W → R) (a : R) :
    {x : W × R // (u x.1 : R) * x.2 + q x.1 = a} ≃ W where
  toFun x := x.1.1
  invFun w := ⟨(w, (↑(u w)⁻¹ : R) * (a - q w)), by simp [← mul_assoc]⟩
  left_inv := by
    rintro ⟨⟨w,t⟩, h⟩
    apply Subtype.ext
    change (w, ↑(u w)⁻¹ * (a - q w)) = (w,t)
    congr 1
    change ↑(u w)⁻¹ * (a - q w) = t
    change (u w : R) * t + q w = a at h
    rw [← h, add_sub_cancel_right, ← mul_assoc]; simp
  right_inv _ := rfl

theorem graph_card {R W : Type*} [CommRing R] [Finite W] (u : W → Rˣ) (q : W → R) (a : R) :
    Nat.card {x : W × R // (u x.1 : R) * x.2 + q x.1 = a} = Nat.card W :=
  Nat.card_congr (graphEquiv u q a)

/-- Probability normalization makes the additive Haar measure invariant under
every ring unit; translation by a transversal-dependent term also preserves it. -/
theorem affine_preserving {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R]
    (ν : Measure R) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] (u : Rˣ) (q : R) :
    MeasurePreserving (fun x : R => (u:R) * x + q) ν ν := by
  let f : R →+ R := AddMonoidHom.mulLeft (u:R)
  have hf : Continuous f := continuous_const.mul continuous_id
  have hsur : Function.Surjective f := by
    intro a
    refine ⟨(↑u⁻¹ : R) * a, ?_⟩
    change (u:R) * (↑u⁻¹ * a) = a
    simp [← mul_assoc]
  haveI : (ν.map f).IsAddHaarMeasure := Measure.isAddHaarMeasure_map_of_isFiniteMeasure ν f hf hsur
  haveI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hp : MeasurePreserving f ν ν := ⟨hf.measurable, Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  exact (measurePreserving_add_right ν q).comp hp

/-- A Haar tube identity for the whole compact unit chart, for a measurable
target of arbitrary shape. The measurable slope may vary with the other
coordinates. This is an exact pushforward, stronger than a residue-count limit. -/
theorem affine_tube {R W : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R] [MeasurableSpace W] (κ : Measure W)
    (ν : Measure R) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (u : W → Rˣ) (q : W → R) (hu : Measurable (fun w => (u w : R))) (hq : Measurable q)
    (S : Set W) (hS : MeasurableSet S) (V : Set R) (hV : MeasurableSet V) :
    (κ.prod ν) {x : W × R | x.1 ∈ S ∧ (u x.1 : R) * x.2 + q x.1 ∈ V} =
      κ S * ν V := by
  classical
  have hset : MeasurableSet {x : W × R | x.1 ∈ S ∧ (u x.1:R) * x.2 + q x.1 ∈ V} :=
    (hS.preimage measurable_fst).inter (hV.preimage (((hu.comp measurable_fst).mul measurable_snd).add
      (hq.comp measurable_fst)))
  rw [Measure.prod_apply hset]
  calc
    _ = ∫⁻ w, S.indicator (fun _ : W => ν V) w ∂κ := by
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ S
      · simpa [hw, Set.preimage, Set.indicator_of_mem] using
          (affine_preserving ν (u w) (q w)).measure_preimage hV.nullMeasurableSet
      · simp [Set.preimage, hw]
    _ = κ S * ν V := by rw [lintegral_indicator_const hS, mul_comm]

end LocalChart
#print axioms LocalChart.graph_card
#print axioms LocalChart.affine_tube
