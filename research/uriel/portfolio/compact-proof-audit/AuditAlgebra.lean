import Mathlib

namespace CompactAudit

theorem auxiliary_transfer {R S T rem a f c bound tol : ℝ}
    (ha : 0 < a) (hf : 0 < f)
    (hid : rem = a * f * (R - S + c * T))
    (hrem : rem ≤ a * f * bound)
    (haux : S - c * T ≤ tol) :
    R ≤ bound + tol := by
  have h := (mul_le_mul_iff_right₀ (mul_pos ha hf)).mp (hid ▸ hrem)
  linarith

theorem rank_deficit {D n h K r : ℝ}
    (hfill : 0 ≤ D - n) (hdef : D - n ≤ r) (hK : 0 ≤ K) (hh : -h ≤ K) :
    n * h ≤ D * h + r * K := by
  have p := mul_le_mul_of_nonneg_left hh hfill
  have q := mul_le_mul_of_nonneg_right hdef hK
  nlinarith only [p, q]

theorem rank_deficit_equality :
    (3 : ℚ) * (-16) = 4 * (-16) + 1 * 16 := by norm_num

theorem selected_card_lower {m s deg card : ℕ} {B x : ℝ}
    (hm : 2 ≤ m) (hpow : m ^ 22 = 2 ^ s) (hdeg : 2 ^ s ≤ deg)
    (hB : B ^ 100 ≤ x) (hx : x ≤ (m : ℝ) ^ 2)
    (hcount : (deg : ℝ) ≤ (card : ℝ) * B) :
    m ^ 21 ≤ card := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by linarith
  have hBm : B ≤ m := by
    by_contra! h
    have hsq : (m : ℝ) ^ 2 < B ^ 2 := pow_lt_pow_left₀ h hmPos.le (by decide)
    have hhigh : B ^ 2 ≤ B ^ 100 := pow_le_pow_right₀ (by linarith) (by decide)
    exact (not_lt_of_ge (hhigh.trans (hB.trans hx))) hsq
  have hnat : m ^ 22 ≤ deg := hpow ▸ hdeg
  have hreal : (m : ℝ) ^ 22 ≤ (deg : ℝ) := by exact_mod_cast hnat
  have hresult : (m : ℝ) ^ 21 ≤ (card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hmPos).mp
    calc
      (m : ℝ) * (m : ℝ) ^ 21 = (m : ℝ) ^ 22 := by ring
      _ ≤ (deg : ℝ) := hreal
      _ ≤ (card : ℝ) * B := hcount
      _ ≤ (card : ℝ) * m := mul_le_mul_of_nonneg_left hBm (by positivity)
      _ = (m : ℝ) * card := mul_comm _ _
  exact_mod_cast hresult

theorem no_transport_to_capacity_32 {m card : ℕ}
    (hm : 2 ≤ m) (hc : m ^ 21 ≤ card) : ¬ card ≤ 32 := by
  have hl : (2 : ℕ) ^ 21 ≤ m ^ 21 := Nat.pow_le_pow_left hm _
  have hi : (32 : ℕ) < 2 ^ 21 := by decide
  exact not_le_of_gt (hi.trans_le (hl.trans hc))

end CompactAudit

#print axioms CompactAudit.auxiliary_transfer
#print axioms CompactAudit.rank_deficit
#print axioms CompactAudit.rank_deficit_equality
#print axioms CompactAudit.selected_card_lower
#print axioms CompactAudit.no_transport_to_capacity_32
