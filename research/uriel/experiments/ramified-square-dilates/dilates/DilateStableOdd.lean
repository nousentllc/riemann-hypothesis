import DilateStableOddCore
import DilateNear
import DilateFineOrbit
import DilateEndpoint

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.StableOdd
open OddCell RamField

/-- Reindex the sharp coefficient theorem at fine precision r+1. -/
theorem central (k r : ℕ) (hk : 1≤k) (hr : 2*k≤r) :
    256^k*TargetOne.count 6 (4^k:S (r+1))=(2*256^k+2)*den (r+1) := by
  have hd : r+1=(r-2*k)+(2*k+1) := by omega
  rw [hd]; exact counts k hk _

private theorem offset (k q : ℕ) :
    ((4:S (2*k+q+1))^k)+center (2*k+q)*pi =
      4^k*(1+2^q*pi) := by
  have h : center (2*k+q)=(4:S (2*k+q+1))^k*2^q := by
    simp only [center,pow_add,pow_mul]
    norm_num
  rw [h]; ring

/-- The moving neighbor at the first later odd precision has relative coefficient
1+2π. Every subsequent neighbor is related by a square of a unit. -/
theorem neighbor (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) :
    256^k*TargetOne.count 6 ((4:S (r+1))^k+center r*pi)=(2*256^k+2)*den (r+1) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2*k≤r)
  rw [offset k q]
  by_cases he : q=1
  · subst q
    have h := near_count (2*k) (by omega)
    have hs : (16:ℕ)^(2*k)=256^k := by rw [pow_mul]; norm_num
    have ha : (2:S (2*k+2))^(2*k)=4^k := by rw [pow_mul]; norm_num
    rw [hs,ha] at h
    simpa only [pow_one] using h
  · rw [deep_companion_count _ _ (by omega)]
    exact central k _ hk (by omega)

/-- The normalized fine-source mixed count equals the stable density at every
odd uniformizer precision 2r+1 ≥ 4k+3, for every unit in its finite ring. -/
theorem stable_mixed (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) (u : (S (r+1))ˣ) :
    256^k*mixedCount r ((4:S (r+1))^k*(u:S (r+1))^2) =
      (2*256^k+2)*(2*den (r+1)) := by
  rw [mul_comm ((4:S (r+1))^k) ((u:S (r+1))^2),mixed_scaled,mixedAt,Nat.mul_add,
    central k r hk (by omega),neighbor k r hk hr]
  ring

/-- At every later odd precision this is the true ratio of normalized field Haar
measures on the integral source lattice and its actual target congruence cell. -/
theorem stable_odd_haar (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := ballAt r ((4:O)^k*(u:O)^2)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      (2+2/256^k:ℝ≥0∞)*lam B := by
  dsimp only
  rw [mul_comm ((4:O)^k) ((u:O)^2)]
  apply haar_pair k r ((4:O)^k) u lam hvol
  · rw [map_pow,map_ofNat]; exact central k r hk (by omega)
  · rw [map_pow,map_ofNat]; exact neighbor k r hk hr

end RamDilate.StableOdd
#print axioms RamDilate.StableOdd.stable_mixed
#print axioms RamDilate.StableOdd.stable_odd_haar
