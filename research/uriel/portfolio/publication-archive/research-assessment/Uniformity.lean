import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace WindowUniformity

/-- A linear function meets every weakened bound with a loss chosen after ε. -/
theorem moving_constants :
    ∀ ε : ℝ, 0 < ε → ∃ eD eL : ℝ, 0 ≤ eD ∧ 0 ≤ eL ∧
      ∀ x : ℝ, 1 ≤ x → x ≤ x ^ ((1:ℝ)/2 + (eD + eL + 7) * ε) := by
  intro ε he
  refine ⟨(2*ε)⁻¹, 0, by positivity, le_rfl, ?_⟩
  intro x hx
  have h : (2*ε)⁻¹*ε = 1/2 := by field_simp
  calc x = x ^ (1:ℝ) := (Real.rpow_one x).symm
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)

/-- The required pointwise bound fails on every full window starting at 2 or later. -/
theorem no_late_windows :
    ¬ ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ ((3:ℝ)/2)), x ≤ x ^ ((3:ℝ)/4) := by
  intro windows
  obtain ⟨Y, hY, bounds⟩ := windows 2
  have hone : 1 < Y := by linarith
  have he : Y ≤ Y ^ ((3:ℝ)/2) := by
    calc Y = Y ^ (1:ℝ) := (Real.rpow_one Y).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hone.le (by norm_num)
  have hstrict : Y ^ ((3:ℝ)/4) < Y := by
    calc _ < Y ^ (1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hone (by norm_num)
         _ = _ := Real.rpow_one Y
  exact (not_le_of_gt hstrict) (bounds Y ⟨le_rfl, he⟩)

#print axioms moving_constants
#print axioms no_late_windows
end WindowUniformity
