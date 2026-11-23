import Mathlib

namespace OddPositionTransport

/-- The part of the leading allowance left at an odd selected top. -/
def charge (b lev t : ℝ) : ℝ := min lev (max 0 (b + lev - t))

theorem charge_full {b lev t : ℝ} (h : t ≤ b) (hlev : 0 ≤ lev) :
    charge b lev t = lev := by
  unfold charge
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

theorem charge_zero {b lev t : ℝ} (h : b + lev ≤ t) (hlev : 0 ≤ lev) :
    charge b lev t = 0 := by
  unfold charge
  rw [max_eq_left (by linarith), min_eq_right hlev]

theorem adjacent_zero {p H B γ β a b : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (hγ : 0 ≤ γ) (ha : H * B ≤ a) (hb : b ≤ B * (1 + β))
    (hcut : p * (1 + γ + β) ≤ H) :
    charge b (B * γ) (a / p) = 0 := by
  apply charge_zero _ (mul_nonneg hB hγ)
  apply (le_div_iff₀ hp).2
  calc
    (b + B * γ) * p ≤ (B * (1 + β) + B * γ) * p := by gcongr
    _ = (p * (1 + γ + β)) * B := by ring
    _ ≤ H * B := mul_le_mul_of_nonneg_right hcut hB
    _ ≤ a := ha

theorem distant_full {p H B α lev a b : ℝ} {d : ℕ} (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hlev : 0 ≤ lev) (hb : B ≤ b) (ha : a ≤ H * (1 + α) * B)
    (hcut : H * (1 + α) ≤ p ^ 3) (hd : 3 ≤ d) :
    charge b lev (a / p ^ d) = lev := by
  apply charge_full _ hlev
  have hp0 : 0 < p := by linarith
  apply (div_le_iff₀ (pow_pos hp0 d)).2
  calc
    a ≤ H * (1 + α) * B := ha
    _ ≤ p ^ 3 * B := mul_le_mul_of_nonneg_right hcut hB
    _ ≤ p ^ d * B := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp hd) hB
    _ ≤ b * p ^ d := by rw [mul_comm b]; gcongr

end OddPositionTransport

#print axioms OddPositionTransport.adjacent_zero
#print axioms OddPositionTransport.distant_full
