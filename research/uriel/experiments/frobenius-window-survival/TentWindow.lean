import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

open Formalism.HC
namespace FrobeniusWindow
noncomputable section

def tentKernel (y v : ℝ) : ℝ :=
  max (v⁻¹-2/y) 0 - 2*max (v⁻¹-(5/2)/y) 0 + max (v⁻¹-3/y) 0

private theorem hinge_identity {z u : ℝ} (hu : 0 ≤ u) :
    max z 0 - 2*max (z-u) 0 + max (z-2*u) 0 = max (min z (2*u-z)) 0 := by
  by_cases a : z ≤ 0
  · rw [max_eq_right a,max_eq_right (sub_nonpos.mpr (a.trans hu)),
      max_eq_right (sub_nonpos.mpr (by linarith)),max_eq_right ((min_le_left _ _).trans a)]
    ring
  · by_cases b : z ≤ u
    · have h0 : 0 ≤ z := le_of_lt (lt_of_not_ge a)
      rw [max_eq_left h0,max_eq_right (sub_nonpos.mpr b), max_eq_right (sub_nonpos.mpr (by linarith)),
        min_eq_left (by linarith),max_eq_left h0]
      ring
    · by_cases c : z ≤ 2*u
      · rw [max_eq_left (by linarith),max_eq_left (by linarith),
          max_eq_right (sub_nonpos.mpr c),min_eq_right (by linarith),max_eq_left (sub_nonneg.mpr c)]
        all_goals try linarith [lt_of_not_ge a,lt_of_not_ge b]
      · rw [max_eq_left (by linarith),max_eq_left (by linarith),
          max_eq_left (by linarith),max_eq_right ((min_le_right _ _).trans (by linarith))]
        all_goals try linarith [lt_of_not_ge a,lt_of_not_ge b,lt_of_not_ge c]

theorem tent_identity {y v : ℝ} (hy : 0 < y) :
    tentKernel y v = max (min (v⁻¹-2/y) (3/y-v⁻¹)) 0 := by
  have h := hinge_identity (z := v⁻¹-2/y) (u := (1/2)/y) (by positivity)
  unfold tentKernel
  convert h using 3 <;> ring

theorem tent_support {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    0 ≤ tentKernel y v ∧ tentKernel y v ≤ 1/(2*y) ∧ tentKernel y v ≤ v⁻¹ ∧
      (tentKernel y v > 0 ↔ y/3 < v ∧ v < y/2) := by
  rw [tent_identity hy]
  have hs : (y/3)⁻¹ = 3/y := by field_simp
  have ht : (y/2)⁻¹ = 2/y := by field_simp
  have hm := min_le_left (v⁻¹-2/y) (3/y-v⁻¹)
  have hn := min_le_right (v⁻¹-2/y) (3/y-v⁻¹)
  refine ⟨le_max_right _ _,max_le ?_ (by positivity),max_le ?_ (by positivity),?_⟩
  · have he : 1/(2*y) = (3/y-2/y)/2 := by ring
    rw [he]
    linarith
  · exact hm.trans (sub_le_self _ (by positivity))
  · change 0 < max (min (v⁻¹-2/y) (3/y-v⁻¹)) 0 ↔ _
    rw [lt_max_iff,or_iff_left (lt_irrefl (0:ℝ)),lt_min_iff,sub_pos,sub_pos,← ht,← hs]
    rw [inv_lt_inv₀ (by positivity : 0 < y/2) hv,inv_lt_inv₀ hv (by positivity : 0 < y/3),and_comm]

def principalSum (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, An.abelian₂ n * max (z / n - 1) 0

theorem log_tent {y : ℝ} (hy : 0 < y) :
    Real.log (y/2)-2*Real.log (2*y/5)+Real.log (y/3) = Real.log (25/24) := by
  have hA : Real.log (y/2)-Real.log (2*y/5) = Real.log (5/4) := by
    rw [← Real.log_div (by positivity : y/2 ≠ 0) (by positivity : 2*y/5 ≠ 0)]
    congr 1
    field_simp <;> norm_num
  have hB : Real.log (y/3)-Real.log (2*y/5) = Real.log (5/6) := by
    rw [← Real.log_div (by positivity : y/3 ≠ 0) (by positivity : 2*y/5 ≠ 0)]
    congr 1
    field_simp <;> norm_num
  have hC : Real.log (5/4) + Real.log (5/6) = Real.log (25/24) := by
    rw [← Real.log_mul (by norm_num : (5/4 : ℝ) ≠ 0) (by norm_num : (5/6 : ℝ) ≠ 0)]
    norm_num
  linarith only [hA,hB,hC]

theorem principal_tent {y : ℝ} (hy : 0 < y) :
    An.G (y/2)/(y/2)-2*(An.G (2*y/5)/(2*y/5))+An.G (y/3)/(y/3) =
    principalSum (y/2)/(y/2)-2*(principalSum (2*y/5)/(2*y/5))+principalSum (y/3)/(y/3) -
      Real.log (25/24) := by
  have hf {v : ℝ} (hv : v ≠ 0) :
      An.G v/v=principalSum v/v-(Real.log v-1-Real.eulerMascheroniConstant) := by
    unfold An.G principalSum
    field_simp
  rw [hf (by positivity : y/2 ≠ 0),hf (by positivity : 2*y/5 ≠ 0),hf (by positivity : y/3 ≠ 0)]
  linarith only [log_tent hy]

open Classical in
theorem nonprincipal_tent {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    An.gChi χ x/(x : ℂ)-2*(An.gChi χ y/(y : ℂ))+An.gChi χ z/(z : ℂ) =
      An.sumLamChi χ x/(x : ℂ)-2*(An.sumLamChi χ y/(y : ℂ))+An.sumLamChi χ z/(z : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  simp only [An.gChi,if_neg hχ]
  field_simp
  ring

end
end FrobeniusWindow

#print axioms FrobeniusWindow.tent_support
#print axioms FrobeniusWindow.principal_tent
#print axioms FrobeniusWindow.nonprincipal_tent
