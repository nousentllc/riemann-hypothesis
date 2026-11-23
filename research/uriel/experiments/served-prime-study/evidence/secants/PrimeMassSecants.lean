import Mathlib

noncomputable section
namespace Uriel.PrimeMass
open Finset

def hinge (t n : ℝ) : ℝ := max (t - n) 0

theorem left_atom (H h n : ℝ) (hH : 0 ≤ H) (hh : 0 ≤ h) :
    H * (hinge H n - hinge (H-h) n) - h * hinge H n ≤
    h * (if n < H then n else 0) := by
  by_cases hn : n < H
  · rw [if_pos hn]
    have hd : hinge H n - hinge (H-h) n ≤ h := by
      unfold hinge
      rw [max_eq_left (by linarith : 0 ≤ H-n)]
      linarith [le_max_left (H-h-n) (0:ℝ)]
    have hmul := mul_le_mul_of_nonneg_left hd hH
    unfold hinge at hmul ⊢
    rw [max_eq_left (by linarith : 0 ≤ H-n)] at hmul ⊢
    linarith only [hmul]
  · rw [if_neg hn]
    have hz : hinge H n = 0 := max_eq_right (by linarith)
    have hz' : hinge (H-h) n = 0 := max_eq_right (by linarith)
    simp [hz, hz']

theorem right_atom (H h n : ℝ) (hH : 0 ≤ H) (hh : 0 ≤ h) :
    h * (if n ≤ H then n else 0) ≤
    H * (hinge (H+h) n - hinge H n) - h * hinge H n := by
  by_cases hn : n ≤ H
  · rw [if_pos hn]
    unfold hinge
    rw [max_eq_left (by linarith : 0 ≤ H+h-n), max_eq_left (by linarith : 0 ≤ H-n)]
    linarith only
  · rw [if_neg hn]
    have hz : hinge H n = 0 := max_eq_right (by linarith)
    have hp := mul_nonneg hH (le_max_right (H+h-n) (0:ℝ))
    rw [hz]
    simpa only [hinge, mul_zero, sub_zero] using hp

/-- For a prime-power atom at n use w=projected von Mangoldt weight/n.
    An arbitrary common linear term beta*t is allowed at the three abscissae. -/
theorem cumulative_bracket {ι : Type*} (S : Finset ι) (pos w : ι → ℝ)
    (H h beta : ℝ) (hH : 0 ≤ H) (hh : 0 ≤ h) (hw : ∀ i ∈ S, 0 ≤ w i) :
    let F := fun t : ℝ => (∑ i ∈ S, w i * hinge t (pos i)) + beta*t
    H*(F H - F (H-h)) - h*F H ≤ h*(∑ i ∈ S, w i * (if pos i < H then pos i else 0)) ∧
    h*(∑ i ∈ S, w i * (if pos i ≤ H then pos i else 0)) ≤ H*(F (H+h)-F H) - h*F H := by
  let A := fun t : ℝ => ∑ i ∈ S, w i * hinge t (pos i)
  have collect (t s : ℝ) :
      (∑ i ∈ S, w i * (H * (hinge t (pos i) - hinge s (pos i)) - h * hinge H (pos i))) =
      H * (A t - A s) - h * A H := by
    unfold A
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have middle (v : ι → ℝ) : (∑ i ∈ S, w i * (h * v i)) = h * (∑ i ∈ S, w i * v i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have lower := Finset.sum_le_sum (s := S) (fun i hi =>
    mul_le_mul_of_nonneg_left (left_atom H h (pos i) hH hh) (hw i hi))
  have upper := Finset.sum_le_sum (s := S) (fun i hi =>
    mul_le_mul_of_nonneg_left (right_atom H h (pos i) hH hh) (hw i hi))
  rw [collect, middle] at lower upper
  dsimp only
  change H * (A H + beta * H - (A (H-h) + beta * (H-h))) - h * (A H + beta * H) ≤ _ ∧
    _ ≤ H * (A (H+h) + beta * (H+h) - (A H + beta * H)) - h * (A H + beta * H)
  constructor
  · linarith only [lower]
  · linarith only [upper]

/-- An individual atom contributes to the bracket width exactly within distance h of H. -/
theorem triangular_atom (H h n : ℝ) (hh : 0 ≤ h) :
    hinge (H+h) n - 2 * hinge H n + hinge (H-h) n = max (h - |n-H|) 0 := by
  unfold hinge
  rcases le_total n H with hn | hn
  · rw [abs_of_nonpos (by linarith : n-H ≤ 0)]
    simp only [max_def]
    split_ifs <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ n-H)]
    simp only [max_def]
    split_ifs <;> linarith

/-- The difference of the two undivided brackets is precisely the weighted triangular window.
This identity is algebraic in the weights. Positivity enters in cumulative_bracket. -/
theorem bracket_width {ι : Type*} (S : Finset ι) (pos w : ι → ℝ)
    (H h beta : ℝ) (hh : 0 ≤ h) :
    let F := fun t : ℝ => (∑ i ∈ S, w i * hinge t (pos i)) + beta*t
    (H * (F (H+h) - F H) - h * F H) - (H * (F H - F (H-h)) - h * F H) =
      H * (∑ i ∈ S, w i * max (h - |pos i - H|) 0) := by
  let A := fun t : ℝ => ∑ i ∈ S, w i * hinge t (pos i)
  have e : A (H+h) - 2 * A H + A (H-h) = ∑ i ∈ S, w i * max (h - |pos i - H|) 0 := by
    unfold A
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← triangular_atom H h (pos i) hh]
    ring
  dsimp only
  change (H * (A (H+h) + beta*(H+h) - (A H + beta*H)) - h*(A H + beta*H)) -
     (H * (A H + beta*H - (A (H-h) + beta*(H-h))) - h*(A H + beta*H)) = _
  rw [← e]
  ring

end Uriel.PrimeMass

set_option pp.fullNames true
#print axioms Uriel.PrimeMass.left_atom
#print axioms Uriel.PrimeMass.right_atom
#print axioms Uriel.PrimeMass.cumulative_bracket
#print axioms Uriel.PrimeMass.triangular_atom
#print axioms Uriel.PrimeMass.bracket_width
