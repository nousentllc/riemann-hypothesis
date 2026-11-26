import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

open Formalism.HC

namespace GlobalFrobenius

noncomputable def normalizedRamp (y v : ℝ) : ℝ := max (v⁻¹ - y⁻¹) 0

/-- Differencing two normalized ramps cancels the centering constant,
    and bounds all low inputs by the same small kernel. -/
theorem ramp_difference_bounds {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    let K := normalizedRamp y v - normalizedRamp (y/3) v
    0 ≤ K ∧ K ≤ 2/y ∧ K ≤ v⁻¹ ∧ (y ≤ v → K = 0) := by
  have hinv : (y/3)⁻¹ = 3/y := by field_simp
  have h0 : 0 ≤ 2/y := by positivity
  have h1 : y⁻¹ ≤ 3/y := by rw [inv_eq_one_div]; gcongr; norm_num
  simp only [normalizedRamp, hinv]
  refine ⟨sub_nonneg.mpr (max_le_max (by linarith) le_rfl), ?_, ?_, ?_⟩
  · apply (sub_le_iff_le_add').mpr
    apply max_le
    · have hh := le_max_left (v⁻¹ - 3/y) (0:ℝ)
      calc
        _ = (v⁻¹ - 3/y) + 2/y := by rw [inv_eq_one_div y]; ring
        _ ≤ _ := by linarith only [hh]
    · exact add_nonneg (le_max_right _ _) h0
  · exact (sub_le_self _ (le_max_right _ _)).trans (max_le (sub_le_self _ (inv_nonneg.mpr hy.le))
        (inv_nonneg.mpr hv.le))
  · intro h
    have hm := (inv_le_inv₀ hv hy).mpr h
    have ha : v⁻¹ - y⁻¹ ≤ 0 := sub_nonpos.mpr hm
    have hb : v⁻¹ - 3/y ≤ 0 := sub_nonpos.mpr (hm.trans h1)
    rw [max_eq_right ha, max_eq_right hb, sub_zero]


open Classical in
/-- The nonprincipal centering term of the original host function cancels
    after division by scale, before any approximation is made. -/
theorem nonprincipal_cancellation {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hc : χ ≠ 1) {y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) :
    An.gChi χ y / (y : ℂ) - An.gChi χ z / (z : ℂ) =
      An.sumLamChi χ y / (y : ℂ) - An.sumLamChi χ z / (z : ℂ) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  simp only [An.gChi, if_neg hc]
  field_simp
  ring

noncomputable def principalSum (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0

/-- The principal centering term in the actual source leaves exactly log 3. -/
theorem principal_cancellation {y : ℝ} (hy : 0 < y) :
    An.G y / y - An.G (y/3) / (y/3) =
      principalSum y / y - principalSum (y/3) / (y/3) - Real.log 3 := by
  have hn {z : ℝ} (hz : z ≠ 0) :
      An.G z / z = principalSum z / z - (Real.log z - 1 - Real.eulerMascheroniConstant) := by
    unfold An.G principalSum
    field_simp
  rw [hn hy.ne', hn (by positivity : y/3 ≠ 0), Real.log_div hy.ne' (by norm_num : (3:ℝ) ≠ 0)]
  ring

end GlobalFrobenius

#print axioms GlobalFrobenius.ramp_difference_bounds

#print axioms GlobalFrobenius.nonprincipal_cancellation
#print axioms GlobalFrobenius.principal_cancellation
