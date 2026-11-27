import CompanionCounts
import DilateStableOddAll

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.Companion
open OddCell RamField StableOdd

/-- The companion is the negative member of the two resolved branches. -/
def mass (k : ℕ) : ℝ≥0∞ := 2-2/256^k

private theorem decrement_le (k : ℕ) : (2:ℝ≥0∞)/256^k ≤ 2 := by
  have h : (1:ℝ≥0∞) ≤ 256^k := one_le_pow₀ (by norm_num)
  simpa using ENNReal.div_le_div_left h 2

theorem mass_real (k : ℕ) : (mass k).toReal = 2-(2:ℝ)/256^k := by
  rw [mass,ENNReal.toReal_sub_of_le (decrement_le k) (by finiteness)]
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]

theorem mass_finite (k : ℕ) : mass k ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) tsub_le_self

theorem mass_positive (k : ℕ) (hk : 1≤k) : 0 < (mass k).toReal := by
  rw [mass_real,sub_pos,div_lt_iff₀ (by positivity)]
  have h : (1:ℝ)<256^k := one_lt_pow₀ (by norm_num) (by omega)
  linarith

/-- Resolve the count on a full coefficient cylinder. -/
theorem count_band (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) (w : S r) :
    256^k*TargetOne.count 6 (target r (2*k) w) + 2*den r = 2*256^k*den r := by
  have h := band (2*k) r (by omega) hr w
  simpa only [pow_mul,show (16:ℕ)^2=256 by decide] using h
private theorem differ (r : ℕ) (a : S (r+1)) : a≠a+center r*pi := by
  intro h
  apply distinct r
  linear_combination h

private theorem children_scaled (r : ℕ) (a s : S (r+1)) (w : (S (r+1))ˣ) :
    pi^(2*r+1) ∣ s-(w:S (r+1))*a ↔ s=(w:S (r+1))*a ∨
    s=(w:S (r+1))*(a+center r*pi) := by
  obtain ⟨x,rfl⟩ := w.mulLeft.surjective s
  change _ ∣ (w:S (r+1))*x - (w:S (r+1))*a ↔
    (w:S (r+1))*x=_ ∨ (w:S (r+1))*x=_
  rw [←mul_sub,w.isUnit.dvd_mul_left,w.isUnit.mul_right_inj,w.isUnit.mul_right_inj]
  exact childrenAt r a x

private theorem ball_pair (r : ℕ) (a : O) (u : Oˣ) :
    let j := r+1
    let v := Units.map (digit j).toMonoidHom u
    let s := digit j a
    ballAt r ((u:O)^2*a) = RamField.cylinder j ((v:S j)^2*s) ∪
      RamField.cylinder j ((v:S j)^2*(s+center r*pi)) := by
  let j := r+1
  let v := Units.map (digit j).toMonoidHom u
  let s := digit j a
  have test (x : O) : (pi:O)^(2*r+1) ∣ x-(u:O)^2*a ↔
      digit j x = (v:S j)^2*s ∨ digit j x=(v:S j)^2*(s+center r*pi) := by
    rw [odd_dvd_iff,map_sub,map_mul,map_pow]
    have h := children_scaled r s (digit j x) (v^2)
    have hv : ((v^2 : (S j)ˣ) : S j) = (v:S j)^2 := rfl
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

/-- A normalized finite measure ratio at a single field digit. -/
private theorem one_tube (k j : ℕ) (t : S j) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1)
    (h : 256^k*TargetOne.count 6 t+2*den j=2*256^k*den j) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (RamField.cylinder j t)) =
      mass k *lam (RamField.cylinder j t) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let _ : Fintype (R j) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let q := (2^j : ℕ)^2
  have cell_mass (z : R j) : lam (RamTransport.residueCell inc (digit j) z) = 1/(q:ℝ≥0∞) := by
    change lam (RamField.cylinder j z) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol j z
  have hc : lam (RamField.cylinder j t)=1/(q:ℝ≥0∞) := cell_mass t
  rw [hc]
  have tube := RamTransport.fiber_count_to_tube inc inc_injective (digit j) lam
      (fun z => (open_cylinder j z).measurableSet) _ cell_mass t
  refine tube.trans ?_
  have hn : (256:ℝ)^k * (TargetOne.count 6 t:ℝ)+2*(q:ℝ)^5 = 2*(256:ℝ)^k*(q:ℝ)^5 := by
    change 256^k * TargetOne.count 6 t + 2*q^5 = 2*256^k*q^5 at h
    exact_mod_cast h
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (ENNReal.mul_ne_top (mass_finite k) (by finiteness))).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    mass_real,
    ENNReal.toReal_one]
  have hq : (q:ℝ) ≠ 0 := by dsimp [q]; positivity
  field_simp
  linarith

/-- Two equal normalized child ratios imply the identical ratio for the
whole odd-depth cell, after any integral unit-square scaling. -/
theorem haar_pair (k r : ℕ) (a : O) (u : Oˣ) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1)
    (h₁ : 256^k*TargetOne.count 6 (digit (r+1) a)+2*den (r+1)=2*256^k*den (r+1))
    (h₂ : 256^k*TargetOne.count 6 (digit (r+1) a+center r*pi)+2*den (r+1)=2*256^k*den (r+1)) :
    let B := ballAt r ((u:O)^2*a)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      mass k *lam B := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let j := r+1
  let v := Units.map (digit j).toMonoidHom u
  let s := digit j a
  let A := RamField.cylinder j ((v:S j)^2*s)
  let B := RamField.cylinder j ((v:S j)^2*(s+center r*pi))
  let T := RamTransport.tube K integers
  let μ := Measure.pi fun _ : TargetOne.Idx => lam
  change μ (T (ballAt r ((u:O)^2*a))) = _*lam _
  have hp : ballAt r ((u:O)^2*a)=A∪B := ball_pair r a u
  have hab : Disjoint A B := disjoint_cyl j (fun h => differ r s ((v.isUnit.pow 2).mul_right_inj.mp h))
  have hTA : T (A ∪ B) = T A ∪ T B := by
    ext x
    change (_ ∧ (_ ∈ A ∨ _ ∈ B)) ↔ (_ ∧ _ ∈ A) ∨ (_ ∧ _ ∈ B)
    tauto
  have hdis : Disjoint (T A) (T B) := Set.disjoint_left.mpr (fun _ ha hb =>
    Set.disjoint_left.mp hab ha.2 hb.2)
  have hmB : MeasurableSet B := (open_cylinder _ _).measurableSet
  have hmT : MeasurableSet (T B) := by
    have hQ : Continuous (TargetOne.Q (R:=K)) := by unfold TargetOne.Q; fun_prop
    have ht := (MeasurableSet.iInter fun i : TargetOne.Idx => integers_open.measurableSet.preimage
      (measurable_pi_apply (X := fun _ : TargetOne.Idx => K) i)).inter (hmB.preimage hQ.measurable)
    convert ht using 1
    ext x; simp [T,RamTransport.tube]
  have hA : μ (T A)=mass k *lam A := one_tube k j _ lam hvol (by rw [TargetFour.scaled]; exact h₁)
  have hB : μ (T B)=mass k *lam B := one_tube k j _ lam hvol (by rw [TargetFour.scaled]; exact h₂)
  rw [hp,hTA,measure_union hdis hmT,measure_union hab hmB,hA,hB,mul_add]


/-- The center in the model order, before unit-square multiplication. -/
def centerAt (k : ℕ) : O := (4:O)^k*(1+pi)

private theorem digit_center (k r : ℕ) : digit r (centerAt k) = target r (2*k) 0 := by
  have hp : digit r (pi:O) = pi := by
    apply QuadraticAlgebra.ext <;> first | exact map_one _ | exact map_zero _
  unfold centerAt target
  rw [map_mul,map_pow,map_ofNat,map_add,map_one,hp,pow_mul]
  simp [pi]
  ring

private theorem digit_child (k r : ℕ) (hr : 2*k+1≤r) :
    digit (r+1) (centerAt k)+center r*pi =
      target (r+1) (2*k) ((2:S (r+1))^(r-(2*k+1))*pi) := by
  rw [digit_center]
  have he : r=(2*k+1)+(r-(2*k+1)) := by omega
  simp only [target,center,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2:S (r+1))^r = 2^(2*k+1)*2^(r-(2*k+1)) by rw [← pow_add,← he]]
  simp only [mul_zero,add_zero]
  ring

/-- Every depth at or after the stated cutoff has the exact Haar tube ratio. -/
theorem all_late (k d : ℕ) (hk : 1≤k) (hd : 4*k+2≤d) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let B := precisionCell d ((u:O)^2*centerAt k)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      mass k * lam B := by
  rcases Nat.even_or_odd d with ⟨j,hj⟩|⟨j,hj⟩
  · rw [show d=2*j by omega]
    dsimp only
    rw [even_cell,map_mul,map_pow]
    apply one_tube k j _ lam hvol
    let v := Units.map (digit j).toMonoidHom u
    change 256^k*TargetOne.count 6 ((v:S j)^2 * digit j (centerAt k)) + 2*den j = _
    rw [TargetFour.scaled,digit_center]
    exact count_band k j hk (by omega) _
  · rw [show d=2*j+1 by omega]
    change let B := ballAt j ((u:O)^2*centerAt k)
           (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) = mass k * lam B
    apply haar_pair k j _ u lam hvol
    · rw [digit_center]; exact count_band k (j+1) hk (by omega) _
    · rw [digit_child k j (by omega)]; exact count_band k (j+1) hk (by omega) _

private theorem same_predecessor (k : ℕ) (u : Oˣ) :
    precisionCell (4*k+1) ((u:O)^2*centerAt k) =
      precisionCell (4*k+1) ((4:O)^k*(u:O)^2) := by
  unfold precisionCell
  congr 1
  ext z
  let a : O := (u:O)^2*centerAt k
  let b : O := (4:O)^k*(u:O)^2
  let p : O := (pi:O)^(4*k+1)
  change p ∣ z-a ↔ p ∣ z-b
  have hp : (pi:O)^4=4 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,pi_sq]; norm_num
  have diff : p ∣ a-b := by
    refine ⟨(u:O)^2,?_⟩
    dsimp [a,b,p,centerAt]
    rw [pow_add,pow_mul,hp]
    ring
  constructor
  · intro h
    convert dvd_add h diff using 1; ring
  · intro h
    convert dvd_sub h diff using 1; ring

theorem predecessor (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let B := precisionCell (4*k+1) ((u:O)^2*centerAt k)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      2*lam B := by
  dsimp only
  rw [same_predecessor]
  exact StableOdd.predecessor k hk u lam hvol

theorem predecessor_diff (k : ℕ) (hk : 1≤k) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := precisionCell (4*k+1) ((u:O)^2*centerAt k)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) ≠
      mass k *lam B := by
  dsimp only
  let B := precisionCell (4*k+1) ((u:O)^2*centerAt k)
  intro h
  have h' := congrArg ENNReal.toReal ((predecessor k hk u lam hvol).symm.trans h)
  change (2*lam B).toReal = (mass k * lam B).toReal at h'
  simp only [ENNReal.toReal_mul,mass_real,ENNReal.toReal_ofNat] at h'
  have hb := cell_positive_finite (4*k+1) ((u:O)^2*centerAt k) lam hvol
  have hp : 0 < (lam B).toReal := ENNReal.toReal_pos hb.1.ne' hb.2.ne
  have hd : 0 < (2:ℝ)/256^k := by positivity
  nlinarith [mul_pos hd hp]

/-- A proposed starting depth gives a stable tail exactly when it is at
least 4k+2. No separate assertion about accidental earlier matches is needed. -/
theorem sharp_stabilization (k n : ℕ) (hk : 1≤k) (u : Oˣ) (lam : Measure K)
    [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (∀ d : ℕ, n≤d →
      let B := precisionCell d ((u:O)^2*centerAt k)
      (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
        mass k *lam B) ↔ 4*k+2≤n := by
  constructor
  · intro h
    by_contra hn
    exact predecessor_diff k hk u lam hvol (h (4*k+1) (by omega))
  · intro hn d hd
    exact all_late k d hk (hn.trans hd) u lam hvol

end RamDilate.Companion
#print axioms RamDilate.Companion.sharp_stabilization
#print axioms RamDilate.Companion.all_late
#print axioms RamDilate.Companion.predecessor
#print axioms RamDilate.Companion.predecessor_diff
