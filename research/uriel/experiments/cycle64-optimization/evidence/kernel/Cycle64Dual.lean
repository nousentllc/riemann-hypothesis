import Mathlib

open scoped BigOperators

namespace Cycle64Dual

/-- A nonnegative toll on the loss at an anchor is paid by coordinate deficits.
The proof takes the ledger identity and the coefficient inequalities as hypotheses. -/
theorem fractional_toll_bound {ι : Type*} (s : Finset ι)
    (rate cap coeff leak : ι → ℝ) (toll anchor baseline num den z : ℝ)
    (hden : 0 < den) (htoll : 0 ≤ toll)
    (hledger : num - z * den =
      toll * (baseline - anchor) - ∑ i ∈ s, coeff i * (cap i - rate i))
    (hcap : ∀ i ∈ s, rate i ≤ cap i)
    (hanchor : baseline - anchor ≤ ∑ i ∈ s, leak i * (cap i - rate i))
    (hcoeff : ∀ i ∈ s, toll * leak i ≤ coeff i) : num / den ≤ z := by
  have hpaid : (∑ i ∈ s, toll * (leak i * (cap i - rate i))) ≤
      ∑ i ∈ s, coeff i * (cap i - rate i) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcoeff i hi) (sub_nonneg.mpr (hcap i hi))
  rw [← Finset.mul_sum] at hpaid
  have hcost := (mul_le_mul_of_nonneg_left hanchor htoll).trans hpaid
  exact (div_le_iff₀ hden).mpr (by linarith)

/-- Averaging 26 finite productive-leaf rates and two anchor rates checks
one convenient rational interior allocation. -/
theorem rational_interior_ledger :
    26 * (299 / 125 : ℚ) + 707 / 1000 + 1101 / 1000 = 64 ∧
    (116 * (299 / 125 : ℚ)) / (2112 + 254 * (299 / 125) + 32 * (707 / 1000)) =
      17342 / 171387 := by
  norm_num

#print axioms fractional_toll_bound
#print axioms rational_interior_ledger

end Cycle64Dual
