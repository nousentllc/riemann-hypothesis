import Cylinders
open MeasureTheory NumberField IsDedekindDomain Topology
noncomputable section
namespace TargetOne
theorem small_cylinder (N : Set K) (hN : N ∈ 𝓝 (1:K)) : ∃ k : ℕ, cylinder (k+3) 1 ⊆ N := by
  have hcont : Continuous inc := continuous_subtype_val.comp ei.continuous
  have hpre : inc ⁻¹' N ∈ 𝓝 (1 : ℤ_[2]) := by
    apply hcont.continuousAt
    simpa only [map_one] using hN
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹ < 1)
  refine ⟨k,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  apply hball
  have h : y ∈ Metric.closedBall (1 : ℤ_[2]) ((2:ℝ)^(-((k+3:ℕ):ℤ))) := by
    rw [←ball_digit]
    simpa only [Set.mem_setOf_eq,map_one] using hy
  have hh : (2:ℝ)^(-((k+3:ℕ):ℤ)) < ε := by
    rw [zpow_neg,zpow_natCast,←inv_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : k ≤ k+3)) hk
  exact Metric.closedBall_subset_ball hh h
end TargetOne
