import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

open Formalism.HC

namespace FrobeniusGain
noncomputable section

def interiorKernel (y v : ℝ) : ℝ := max (v⁻¹-2/y) 0 - max (v⁻¹-3/y) 0

theorem interior_kernel {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    0 ≤ interiorKernel y v ∧ interiorKernel y v ≤ 1/y ∧
    interiorKernel y v ≤ v⁻¹ ∧ (y/2 ≤ v → interiorKernel y v = 0) := by
  have h12 : 2/y ≤ 3/y := by gcongr; norm_num
  have h0 : 0 ≤ 1/y := by positivity
  unfold interiorKernel
  refine ⟨sub_nonneg.mpr (max_le_max (by linarith) le_rfl), ?_, ?_, ?_⟩
  · apply (sub_le_iff_le_add').mpr
    apply max_le
    · have hh := le_max_left (v⁻¹-3/y) (0:ℝ)
      have hr : v⁻¹-2/y = v⁻¹-3/y+1/y := by ring
      linarith only [hh,hr]
    · exact add_nonneg (le_max_right _ _) h0
  · exact (sub_le_self _ (le_max_right _ _)).trans
      (max_le (sub_le_self _ (by positivity)) (inv_nonneg.mpr hv.le))
  · intro h
    have hm := (inv_le_inv₀ hv (by positivity : 0 < y/2)).mpr h
    have hh : (y/2)⁻¹ = 2/y := by field_simp
    rw [hh] at hm
    rw [max_eq_right (sub_nonpos.mpr hm),max_eq_right (sub_nonpos.mpr (hm.trans h12)),sub_zero]

def principalSum (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y/n-1) 0

/-- The exact principal term in the original host function,
at the two interior endpoints. -/
theorem principal_interior {y : ℝ} (hy : 0 < y) :
    An.G (y/2)/(y/2) - An.G (y/3)/(y/3) =
      principalSum (y/2)/(y/2) - principalSum (y/3)/(y/3) - Real.log (3/2) := by
  have hn {z : ℝ} (hz : z ≠ 0) :
      An.G z/z = principalSum z/z - (Real.log z - 1 - Real.eulerMascheroniConstant) := by
    unfold An.G principalSum
    field_simp
  rw [hn (by positivity : y/2 ≠ 0),hn (by positivity : y/3 ≠ 0)]
  have hlog : Real.log (y/2) - Real.log (y/3) = Real.log (3/2) := by
    rw [← Real.log_div (by positivity : y/2 ≠ 0) (by positivity : y/3 ≠ 0)]
    congr 1
    field_simp
  linarith only [hlog]

end
end FrobeniusGain

#print axioms FrobeniusGain.interior_kernel
#print axioms FrobeniusGain.principal_interior
