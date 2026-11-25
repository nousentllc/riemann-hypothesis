import GaussianDilates
import SingularGaussian
open TargetOne HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace DyadicWave

theorem zero_tube_ratio (r : ℕ) : normCount r 0=1 := by
  induction r using Nat.twoStepInduction with
  | zero =>
    have h : count 6 (0:ZMod 1)=1 := by rw [Subsingleton.elim (0:ZMod 1) 1,small_1]
    change (count 6 (0:ZMod 1):ℚ)/1=1
    rw [h]; norm_num
  | one =>
    have h : count 6 (0:ZMod 2)=32 := by
      simpa only [show (4:ZMod 2)=0 by decide] using TargetFour.base_2
    change (count 6 (0:ZMod 2):ℚ)/32=1
    rw [h]; norm_num
  | more r hr _ =>
    have h := norm_step r 0
    rw [Nat.mul_zero,hr] at h
    norm_num at h
    exact h

theorem zero_tube_measure (lam : Measure K) [lam.IsAddHaarMeasure] [SigmaFinite lam]
    (hlam : lam (O : Set K)=1) (r : ℕ) :
    (Measure.pi fun _ : Idx => lam) (tube r 0) = lam (cylinder r 0) := by
  rw [tube_mass lam hlam,cyl_mass lam hlam]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_one,ENNReal.toReal_ofNat]
  have hr := zero_tube_ratio r
  unfold normCount at hr
  have h : (count 6 (0:ZMod (2^r)):ℝ)/(2^r:ℝ)^5=1 := by
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,Nat.cast_zero]
      using congrArg (fun z : ℚ => (z:ℝ)) hr
  field_simp at h ⊢
  linear_combination h

theorem sharp_floor (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) (t : ℕ) (ht : t≠0) :
    (3/4:ℝ) ≤ (m (hermScal K conjG ((t^2:ℕ):K)) lattice).toReal := by
  obtain ⟨k,u,hu,rfl⟩ := Nat.exists_eq_two_pow_mul_odd ht
  rw [show (2^k*u)^2=4^k*u^2 by rw [mul_pow,←pow_mul, Nat.mul_comm k 2,pow_mul]; norm_num,
      fiber_mass lam hlam m hm k u hu,ENNReal.coe_toReal]
  change (3/4:ℝ) ≤ ((density k:ℚ):ℝ)
  suffices h : (3/4:ℚ) ≤ density k by
    have H : ((3/4:ℚ):ℝ) ≤ ((density k:ℚ):ℝ) := Rat.cast_le.2 h
    simpa only [Rat.cast_div,Rat.cast_ofNat] using H
  have hp : (1:ℚ) ≤ 16^k := one_le_pow₀ (by norm_num)
  have hq : 1/(4*(16:ℚ)^k) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  dsimp [density]; linarith

theorem sharp_witness (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) :
    (m (hermScal K conjG 1) lattice).toReal=3/4 := target_one lam hlam m hm

end DyadicWave
#print axioms DyadicWave.zero_tube_ratio
#print axioms DyadicWave.sharp_floor
