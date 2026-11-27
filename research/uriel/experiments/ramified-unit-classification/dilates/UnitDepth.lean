import UnitCells

/-! Sharpness of the common cutoff on the entire valuation shell. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.UnitClass
open RamField OddCell StableOdd

private theorem same_predecessor (k : ℕ) (u : Oˣ) :
    precisionCell (4*k+1) ((4:O)^k*(u:O)) = precisionCell (4*k+1) ((4:O)^k) := by
  obtain ⟨w,hw⟩ := decomposition u
  let c : O := if bit u then 1 else 0
  have hrep : (representative (bit u):O)=1+pi*c := by
    dsimp [c]
    cases bit u <;> simp [representative,pi]
  rw [hrep] at hw
  unfold precisionCell
  congr 1
  ext z
  let a : O := (4:O)^k*(u:O)
  let b : O := (4:O)^k
  let p : O := (pi:O)^(4*k+1)
  change p ∣ z-a ↔ p ∣ z-b
  have hp : (pi:O)^4=4 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,pi_sq]; norm_num
  have diff : p ∣ a-b := by
    refine ⟨c+pi*w,?_⟩
    dsimp only [a,b,p]
    rw [pow_add,pow_mul,hp,hw,←pi_sq]
    ring
  constructor
  · intro h
    convert dvd_add h diff using 1; ring
  · intro h
    convert dvd_sub h diff using 1; ring

theorem predecessor (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let B := precisionCell (4*k+1) ((4:O)^k*(u:O))
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      2*lam B := by
  dsimp only
  rw [same_predecessor]
  simpa only [Units.val_one,one_pow,mul_one] using StableOdd.predecessor k hk (1:Oˣ) lam hvol

private theorem predecessor_diff (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let B := precisionCell (4*k+1) ((4:O)^k*(u:O))
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) ≠
      mass k (bit u)*lam B := by
  dsimp only
  let B := precisionCell (4*k+1) ((4:O)^k*(u:O))
  intro h
  have e := congrArg ENNReal.toReal ((predecessor k hk u lam hvol).symm.trans h)
  change (2*lam B).toReal=(mass k (bit u)*lam B).toReal at e
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,mass_real] at e
  have hb := cell_positive_finite (4*k+1) ((4:O)^k*(u:O)) lam hvol
  have hp : 0<(lam B).toReal := ENNReal.toReal_pos hb.1.ne' hb.2.ne
  have hd : 0 < (2:ℝ)/256^k := by positivity
  cases hb' : bit u <;> simp only [hb',Bool.false_eq_true,if_false,if_true] at e <;> nlinarith [mul_pos hd hp]

theorem sharp_stabilization (k n : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    (∀ d : ℕ, n≤d →
      let B := precisionCell d ((4:O)^k*(u:O))
      (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
        mass k (bit u)*lam B) ↔ 4*k+2≤n := by
  constructor
  · intro h
    by_contra hn
    exact predecessor_diff k hk u lam hvol (h (4*k+1) (by omega))
  · intro hn d hd
    exact all_late k d hk (hn.trans hd) u lam hvol

end RamDilate.UnitClass
#print axioms RamDilate.UnitClass.predecessor
#print axioms RamDilate.UnitClass.sharp_stabilization
