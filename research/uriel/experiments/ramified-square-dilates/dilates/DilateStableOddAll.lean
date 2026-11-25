import DilateStableOdd

/-! Uniformizer precision is counted one π power at a time. This final
statement treats every depth, independently of parity, on a single kind of cell. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.StableOdd
open OddCell RamField

/-- An integral target neighborhood defined by its actual uniformizer ideal. -/
def precisionCell (d : ℕ) (a : O) : Set K := inc '' {x : O | (pi:O)^d ∣ x-a}

private theorem digit_zero (j : ℕ) (x : O) : (2:O)^j ∣ x ↔ digit j x=0 := by
  constructor
  · rintro ⟨w,rfl⟩
    have hh : (2:ZMod (2^j))^j=0 := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^j)
    have z : (2:S j)^j=0 := by
      simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (ZMod (2^j)) (S j)) hh
    rw [map_mul,map_pow,map_ofNat,z,zero_mul]
  · intro hx
    have one (z : ℤ_[2]) (h : PadicInt.toZModPow j z=0) : (2:ℤ_[2])^j ∣ z := by
      change z ∈ RingHom.ker (PadicInt.toZModPow j) at h
      rwa [PadicInt.ker_toZModPow,Ideal.mem_span_singleton] at h
    obtain ⟨a,ha⟩ := one x.re (congrArg QuadraticAlgebra.re hx)
    obtain ⟨b,hb⟩ := one x.im (congrArg QuadraticAlgebra.im hx)
    refine ⟨⟨a,b⟩,?_⟩
    have hsp : (2:O)^j=((2^j:ℕ):O) := by simp
    rw [hsp]
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast] <;> simp [ha,hb]

theorem even_cell (j : ℕ) (a : O) :
    precisionCell (2*j) a = RamField.cylinder j (digit j a) := by
  unfold precisionCell RamField.cylinder
  congr 1
  ext x
  change (pi:O)^(2*j) ∣ x-a ↔ digit j x=digit j a
  rw [pow_mul,pi_sq,digit_zero,map_sub,sub_eq_zero]

/-- Every uniformizer depth from 4k+2 onward has exactly the limiting ratio.
The quantifier covers odd and even values, for every integral unit. -/
theorem all_late (k d : ℕ) (hk : 1≤k) (hd : 4*k+2≤d) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := precisionCell d ((4:O)^k*(u:O)^2)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      (2+2/256^k:ℝ≥0∞)*lam B := by
  rcases Nat.even_or_odd d with ⟨j,hj⟩|⟨j,hj⟩
  · have h : d=2*j := by omega
    rw [h]
    dsimp only
    rw [even_cell]
    apply DilateTransport.tube k j u lam hvol
    have he : j=(j-(2*k+1))+(2*k+1) := by omega
    rw [he]; exact counts k hk _
  · have h : d=2*j+1 := by omega
    rw [h]
    exact stable_odd_haar k j hk (by omega) u lam hvol

/-- At the immediately preceding depth, the exact ambient ratio is two. -/
theorem predecessor (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := precisionCell (4*k+1) ((4:O)^k*(u:O)^2)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) = 2*lam B := by
  rw [show 4*k+1=2*(2*k)+1 by omega]
  exact last_odd_haar k hk u lam hvol

/-- The target-cell Haar mass is strictly positive and finite. Every such cell
contains its d-th full coefficient cylinder, and is contained in the order. -/
theorem cell_positive_finite (d : ℕ) (a : O) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers=1) : 0 < lam (precisionCell d a) ∧ lam (precisionCell d a) < ⊤ := by
  have inside : RamField.cylinder d (digit d a) ⊆ precisionCell d a := by
    rintro x ⟨z,hz,rfl⟩
    refine ⟨z,?_,rfl⟩
    have e : digit d (z-a)=0 := by rw [map_sub,show digit d z=digit d a from hz,sub_self]
    have hpow : (pi:O)^d ∣ (2:O)^d := by
      rw [←pi_sq,←pow_mul]
      exact pow_dvd_pow _ (by omega)
    exact dvd_trans hpow ((digit_zero d _).mpr e)
  have outside : precisionCell d a ⊆ integers := fun _ ⟨z,_,hz⟩ => ⟨z,hz⟩
  constructor
  · apply lt_of_lt_of_le _ (measure_mono inside)
    rw [cyl_mass lam hvol]; exact ENNReal.div_pos one_ne_zero (by finiteness)
  · exact lt_of_le_of_lt (measure_mono outside) (show lam integers < ⊤ by rw [hvol]; exact ENNReal.one_lt_top)

theorem predecessor_diff (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := precisionCell (4*k+1) ((4:O)^k*(u:O)^2)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) ≠
      (2+2/256^k:ℝ≥0∞)*lam B := by
  dsimp only
  let B := precisionCell (4*k+1) ((4:O)^k*(u:O)^2)
  intro h
  have h' := congrArg ENNReal.toReal ((predecessor k hk u lam hvol).symm.trans h)
  change (2*lam B).toReal = ((2+2/256^k)*lam B).toReal at h'
  simp only [ENNReal.toReal_mul,ENNReal.toReal_add (a:=2) (b:=2/256^k) (by finiteness) (by finiteness),
    ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at h'
  have hb := cell_positive_finite (4*k+1) ((4:O)^k*(u:O)^2) lam hvol
  have hp : 0 < (lam B).toReal := ENNReal.toReal_pos hb.1.ne' hb.2.ne
  have hd : 0 < (2:ℝ)/256^k := by positivity
  nlinarith [mul_pos hd hp]

/-- A proposed starting depth gives a stable tail exactly when it is at
least 4k+2. No separate assertion about accidental earlier matches is needed. -/
theorem sharp_stabilization (k n : ℕ) (hk : 1≤k) (u : Oˣ) (lam : Measure K)
    [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (∀ d : ℕ, n≤d →
      let B := precisionCell d ((4:O)^k*(u:O)^2)
      (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
        (2+2/256^k:ℝ≥0∞)*lam B) ↔ 4*k+2≤n := by
  constructor
  · intro h
    by_contra hn
    exact predecessor_diff k hk u lam hvol (h (4*k+1) (by omega))
  · intro hn d hd
    exact all_late k d hk (hn.trans hd) u lam hvol

end RamDilate.StableOdd
#print axioms RamDilate.StableOdd.all_late
#print axioms RamDilate.StableOdd.predecessor
#print axioms RamDilate.StableOdd.sharp_stabilization
