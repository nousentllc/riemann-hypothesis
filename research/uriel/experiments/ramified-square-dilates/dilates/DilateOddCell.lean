import DilateOddCellOrder
import DilateCompanion

/-! The last intervening uniformizer digit still averages the two opposite
deviations. The denominator is twice the full-precision normalization because
the target condition covers two fine target cells. -/
noncomputable section
namespace RamDilate.OddCell

theorem square_center (k : ℕ) : center (2*k) = (4:S (2*k+1))^k := by
  simp only [center,Nat.cast_pow,Nat.cast_ofNat,pow_mul]
  norm_num

/-- Every unit-square twist has twice its two-cell normalization. -/
theorem last_odd (k : ℕ) (hk : 1≤k) (u : (S (2*k+1))ˣ) :
    mixedCount (2*k) ((4:S (2*k+1))^k * (u:S (2*k+1))^2) = 2*(2*den (2*k+1)) := by
  rw [mul_comm ((4:S (2*k+1))^k) ((u:S (2*k+1))^2),mixed_scaled,←square_center,mixed_sum,square_center,companion_pair k hk]
  ring

/-- The integral test for any target equals the finite congruence used by
mixedCount. The statement includes the full six-variable polynomial. -/
theorem order_test (r : ℕ) (a : RamField.O) (x : Fin 6 → RamField.O) :
    (pi:RamField.O)^(2*r+1) ∣ TargetOne.sqSum x - a ↔
    (pi:S (r+1))^(2*r+1) ∣ TargetOne.sqSum (fun i => RamField.digit (r+1) (x i)) -
      RamField.digit (r+1) a := by
  rw [odd_dvd_iff,map_sub]
  simp only [TargetOne.sqSum,map_sum,map_pow]

end RamDilate.OddCell
#print axioms RamDilate.OddCell.last_odd
#print axioms RamDilate.OddCell.order_test
