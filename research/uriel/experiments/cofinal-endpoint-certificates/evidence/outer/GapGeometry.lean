import Mathlib

namespace OuterGap

/-- Logarithmic interface, with q=J/4. Scaling the bounds avoids division;
    all lower thresholds stay inside the universal quantifier. -/
def Supply (S : Set ℝ) (q c U₀ : ℝ) : Prop :=
  ∀ U ≥ U₀, ∃ w : ℝ, U ≤ 4*q*w ∧ 2*w ≤ U ∧
    Set.Icc w (min (2*w) (U-c)) ⊆ S

theorem saturation {S : Set ℝ} {q c U₀ v : ℝ} (H : Supply S q c U₀)
    (hq : 0 < q) (hu : q ≤ 1) (hv : 0 ≤ v) (hc : c ≤ v) (hU : U₀ ≤ 2*v) :
    v ∈ S := by
  obtain ⟨w, hl, hr, hS⟩ := H (2*v) hU
  have hw : 0 ≤ w := by
    by_contra! hn
    nlinarith [mul_neg_of_pos_of_neg hq hn]
  have hs : q*w ≤ w := by simpa using mul_le_mul_of_nonneg_right hu hw
  apply hS
  exact ⟨by linarith, le_min (by linarith) (by linarith)⟩

theorem closedHit {S : Set ℝ} {q c U₀ L : ℝ} (H : Supply S q c U₀)
    (hq : 1 ≤ q) (hl : 0 ≤ L) (hc : c ≤ L) (hU : U₀ ≤ 2*L) :
    ∃ v ∈ S, L ≤ v ∧ v ≤ q*L := by
  have hL : L ≤ q*L := by simpa using mul_le_mul_of_nonneg_right hq hl
  obtain ⟨w, hw, ht, hS⟩ := H (2*q*L) (by linarith)
  have hqw : 0 < q := by linarith
  have h2 : L ≤ 2*w := by
    by_contra! hh
    nlinarith [mul_lt_mul_of_pos_left hh hqw]
  have hn : 0 ≤ w := by linarith
  refine ⟨max L w,hS ⟨le_max_right _ _, le_min ?_ ?_⟩,le_max_left _ _,?_⟩
  · exact max_le h2 (by linarith)
  · exact max_le (by linarith) (by linarith)
  · exact max_le hL (by linarith)

#print axioms OuterGap.saturation
#print axioms OuterGap.closedHit

end OuterGap
