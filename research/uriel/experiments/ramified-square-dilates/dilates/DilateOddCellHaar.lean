import DilateOddCell
import DilateTransportCells

/-! The mixed count is the exact Haar tube ratio on the last odd target
cell, for every integral unit of the modeled coefficient order. -/
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace RamDilate.OddCell
open RamField

/-- A true congruence cell in the coefficient order, viewed in the local field. -/
def ballAt (r : ℕ) (a : O) : Set K := inc '' {x : O | (pi:O)^(2*r+1) ∣ x-a}

private theorem unitChildren (r : ℕ) (s : S (r+1)) (w : (S (r+1))ˣ) :
    pi^(2*r+1) ∣ s-(w:S (r+1))*center r ↔
      s=(w:S (r+1))*center r ∨ s=(w:S (r+1))*(center r*(1+pi)) := by
  obtain ⟨x,rfl⟩ := w.mulLeft.surjective s
  change _ ∣ (w:S (r+1))*x - (w:S (r+1))*center r ↔
    (w:S (r+1))*x=_ ∨ (w:S (r+1))*x=_
  rw [←mul_sub,w.isUnit.dvd_mul_left,w.isUnit.mul_right_inj,w.isUnit.mul_right_inj]
  exact children r x

private theorem ball_children (r : ℕ) (u : Oˣ) :
    let v := Units.map (digit (r+1)).toMonoidHom u
    ballAt r ((u:O)^2*2^r) = RamField.cylinder (r+1) ((v:S (r+1))^2*center r) ∪
      RamField.cylinder (r+1) ((v:S (r+1))^2*(center r*(1+pi))) := by
  let v := Units.map (digit (r+1)).toMonoidHom u
  have test (x : O) : (pi:O)^(2*r+1) ∣ x-(u:O)^2*2^r ↔
        digit (r+1) x=(v:S (r+1))^2*center r ∨
        digit (r+1) x=(v:S (r+1))^2*(center r*(1+pi)) := by
    rw [odd_dvd_iff,map_sub,map_mul,map_pow,map_pow,map_ofNat]
    have hv : ((v^2 : (S (r+1))ˣ) : S (r+1)) = (v:S (r+1))^2 := rfl
    have hu : digit (r+1) (u:O) = (v:S (r+1)) := rfl
    have hs : center r = (2:S (r+1))^r := by simp [center]
    rw [hu,←hs]
    have h := unitChildren r (digit (r+1) x) (v^2)
    rw [hv] at h
    exact h
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    rcases (test z).mp hz with h|h
    · exact Or.inl ⟨z,h,rfl⟩
    · exact Or.inr ⟨z,h,rfl⟩
  · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
    · exact ⟨z,(test z).mpr (Or.inl hz),rfl⟩
    · exact ⟨z,(test z).mpr (Or.inr hz),rfl⟩

private theorem ratio (n m q : ℕ) (hq : q ≠ 0) (hm : n+m=4*q^5) :
    (n:ℝ≥0∞)*(1/(q:ℝ≥0∞))^6 + (m:ℝ≥0∞)*(1/(q:ℝ≥0∞))^6 =
      2*(1/(q:ℝ≥0∞)+1/(q:ℝ≥0∞)) := by
  rw [←add_mul,←Nat.cast_add,hm]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_mul,
    ENNReal.toReal_add (a:=1/(q:ℝ≥0∞)) (b:=1/(q:ℝ≥0∞)) (by finiteness) (by finiteness),
    ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  field_simp
  ring

/-- At precision 4k+1 the actual Haar tube still has ratio exactly two.
Its two depth-(4k+2) target children have equal target Haar measure. -/
theorem last_odd_haar (k : ℕ) (hk : 1≤k) (u : Oˣ) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1) :
    let B := ballAt (2*k) ((4:O)^k*(u:O)^2)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) = 2*lam B := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let r := 2*k
  let j := r+1
  let _ : Fintype (R j) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let v := Units.map (digit j).toMonoidHom u
  let a := (v:R j)^2 * center r
  let b := (v:R j)^2 * (center r * (1+pi))
  let A := RamField.cylinder j a
  let B := RamField.cylinder j b
  let T := RamTransport.tube K integers
  let μ := Measure.pi fun _ : TargetOne.Idx => lam
  have hident : ballAt r ((4:O)^k*(u:O)^2) = A∪B := by
    have e : (2:O)^(2*k)=4^k := by rw [pow_mul]; norm_num
    simpa only [r,e,mul_comm ((4:O)^k) ((u:O)^2)] using ball_children r u
  change μ (T (ballAt r ((4:O)^k*(u:O)^2))) = 2*lam _
  have hab : Disjoint A B := disjoint_cyl j (fun h => distinct r ((v.isUnit.pow 2).mul_right_inj.mp h))
  have hTA : T (A ∪ B) = T A ∪ T B := by
    ext x
    change (_ ∧ (_ ∈ A ∨ _ ∈ B)) ↔ (_ ∧ _ ∈ A) ∨ (_ ∧ _ ∈ B)
    tauto
  have hdis : Disjoint (T A) (T B) := Set.disjoint_left.mpr (fun _ ha hb =>
    Set.disjoint_left.mp hab ha.2 hb.2)
  have hmB : MeasurableSet B := (open_cylinder j b).measurableSet
  have hmT : MeasurableSet (T B) := by
    have hQ : Continuous (TargetOne.Q (R:=K)) := by unfold TargetOne.Q; fun_prop
    have ht := (MeasurableSet.iInter fun i : TargetOne.Idx => integers_open.measurableSet.preimage
      (measurable_pi_apply (X := fun _ : TargetOne.Idx => K) i)).inter (hmB.preimage hQ.measurable)
    convert ht using 1
    ext x; simp [T,RamTransport.tube]
  let q := (2^j : ℕ)^2
  have mass (t : R j) : lam (RamTransport.residueCell inc (digit j) t) = 1/(q:ℝ≥0∞) := by
    change lam (RamField.cylinder j t) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol j t
  have massC (t : R j) : lam (RamField.cylinder j t)=1/(q:ℝ≥0∞) := mass t
  have massT (t : R j) : μ (T (RamField.cylinder j t)) = (TargetOne.count 6 t:ℝ≥0∞)*(1/(q:ℝ≥0∞))^6 :=
    RamTransport.fiber_count_to_tube inc inc_injective (digit j) lam
      (fun z => (open_cylinder j z).measurableSet) _ mass t
  rw [hident,hTA,measure_union hdis hmT,measure_union hab hmB]
  change μ (T (RamField.cylinder j a))+μ (T (RamField.cylinder j b)) = 2*(lam (RamField.cylinder j a)+lam (RamField.cylinder j b))
  rw [massT,massT,massC,massC]
  apply ratio _ _ q (by dsimp [q]; positivity)
  change TargetOne.count 6 (((v:R j)^2)*center r) +
    TargetOne.count 6 (((v:R j)^2)*(center r*(1+pi))) = _
  rw [TargetFour.scaled v,TargetFour.scaled v]
  change TargetOne.count 6 (center (2*k)) + TargetOne.count 6 (center (2*k)*(1+pi)) = 4*den (2*k+1)
  rw [square_center]; exact companion_pair k hk

end RamDilate.OddCell
#print axioms RamDilate.OddCell.last_odd_haar
