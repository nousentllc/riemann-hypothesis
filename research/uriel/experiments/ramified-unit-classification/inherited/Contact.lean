import Mathlib
open MeasureTheory Topology Filter
open scoped ENNReal NNReal
namespace TargetOne
theorem contact {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (U : Set X) (hu : IsOpen U) {s : X} (hs : s ∈ U)
    (g : X → ℝ) (hg : ContinuousOn g U) (D : ℝ)
    (cert : ∀ N ∈ 𝓝 s, ∃ C : Set X, IsCompact C ∧ C ⊆ U ∩ N ∧ 0 < μ.real C ∧
        ∫ z in C, g z ∂μ = D * μ.real C) : g s = D := by
  have hc := hg.continuousAt (hu.mem_nhds hs)
  by_contra he
  rcases lt_or_gt_of_ne he with h|h
  · let a := (g s+D)/2
    have ha : g s < a := by dsimp [a]; linarith
    obtain ⟨C,hC,hsub,hp,hint⟩ := cert _ (hc (Iio_mem_nhds ha))
    have hi : IntegrableOn g C μ := (hg.mono (hsub.trans Set.inter_subset_left)).integrableOn_compact hC
    have hle : ∫ z in C, g z ∂μ ≤ ∫ _ in C, a ∂μ :=
      setIntegral_mono_on hi (integrableOn_const hC.measure_lt_top.ne) hC.measurableSet
        (fun x hx => (show g x < a from (hsub hx).2).le)
    rw [hint,setIntegral_const,smul_eq_mul] at hle
    have h' : a < D := by dsimp [a]; linarith
    nlinarith [mul_lt_mul_of_pos_right h' hp]
  · let a := (g s+D)/2
    have ha : a < g s := by dsimp [a]; linarith
    obtain ⟨C,hC,hsub,hp,hint⟩ := cert _ (hc (Ioi_mem_nhds ha))
    have hi : IntegrableOn g C μ := (hg.mono (hsub.trans Set.inter_subset_left)).integrableOn_compact hC
    have hle : ∫ _ in C, a ∂μ ≤ ∫ z in C, g z ∂μ :=
      setIntegral_mono_on (integrableOn_const hC.measure_lt_top.ne) hi hC.measurableSet
        (fun x hx => (show a < g x from (hsub hx).2).le)
    rw [hint,setIntegral_const,smul_eq_mul] at hle
    have h' : D < a := by dsimp [a]; linarith
    nlinarith [mul_lt_mul_of_pos_right h' hp]
end TargetOne
