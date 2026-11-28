import Mathlib

open scoped BigOperators

namespace GainGapTransport

/-- One orbit, one lift. The common tax belongs to both alternatives. -/
theorem branch_gap (q tax specialized fallback : ℝ) :
    q + tax - max specialized fallback =
      min (q + tax - specialized) (q + tax - fallback) := by
  rcases le_total specialized fallback with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
  · rw [max_eq_left h, min_eq_left (by linarith)]

/-- Saved fallback cost relative to the specialized-only comparison. -/
theorem recovery (q tax a f : ℝ) :
    q + tax - max a f = q + tax - a - max (f - a) 0 := by
  rcases le_total a f with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- A matched successor can use no more extra allowance than its own offset. -/
theorem matched_offset (b u t : ℝ) (hu : 0 ≤ u) :
    min t (b + u) - min t b ≤ u := by
  rcases le_total t b with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]; linarith
  · rw [min_eq_right h]
    linarith [min_le_right t (b + u)]

/-- A one-orbit lower bound, after paying all nearest-even charges. -/
theorem winning_lower
    (q gu price atax evMin edgeMin pairedOffset allOffset unmatched lev thinLoss kappaLoss : ℝ)
    (hgu : gu ≤ q + evMin)
    (hmass : evMin ≤ edgeMin + pairedOffset + thinLoss)
    (htax : edgeMin ≤ atax)
    (hpr : allOffset - kappaLoss ≤ price)
    (hun : unmatched * lev ≤ allOffset - pairedOffset) :
    unmatched * lev - (thinLoss + kappaLoss) ≤ q + atax - (gu - price) := by
  linarith

/-- The positive lower allowance applies only on lifts where the specialized branch wins. -/
theorem selected_lower (q tax a f amount err : ℝ) (hf : f ≤ q) (ht : 0 ≤ tax)
    (he : 0 ≤ err) (hs : amount - err ≤ q + tax - a) :
    (if f ≤ a then amount else 0) - err ≤ q + tax - max a f := by
  split_ifs with h
  · rw [max_eq_left h]; exact hs
  · rw [max_eq_right (le_of_not_ge h)]; linarith

/-- A matched-edge tax can force a positive deficit whichever branch wins. -/
theorem two_branch_lower (q tax a f unpaired matched err : ℝ) (hf : f ≤ q)
    (ht : matched ≤ tax) (he : 0 ≤ err) (hs : unpaired - err ≤ q + tax - a) :
    min unpaired matched - err ≤ q + tax - max a f := by
  rw [branch_gap]
  exact le_min (by linarith [min_le_left unpaired matched])
    (by linarith [min_le_right unpaired matched])

end GainGapTransport

#print axioms GainGapTransport.branch_gap
#print axioms GainGapTransport.recovery
#print axioms GainGapTransport.matched_offset
#print axioms GainGapTransport.winning_lower
#print axioms GainGapTransport.selected_lower
#print axioms GainGapTransport.two_branch_lower
