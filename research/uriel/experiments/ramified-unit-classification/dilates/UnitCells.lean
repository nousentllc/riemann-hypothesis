import UnitResidue
import UnitCounts

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.UnitClass
open OddCell RamField StableOdd

def mass (k : ℕ) (b : Bool) : ℝ≥0∞ :=
  if b then Companion.mass k else 2+2/256^k

theorem mass_real (k : ℕ) (b : Bool) :
    (mass k b).toReal = if b then 2-(2:ℝ)/256^k else 2+(2:ℝ)/256^k := by
  cases b
  · simp only [mass,Bool.false_eq_true,if_false,
      ENNReal.toReal_add (a := 2) (b := 2/256^k) (by finiteness) (by finiteness),ENNReal.toReal_div,
      ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  · exact Companion.mass_real k

theorem mass_finite (k : ℕ) (b : Bool) : mass k b ≠ ⊤ := by
  cases b
  · change (2+2/256^k:ℝ≥0∞) ≠ ⊤
    finiteness
  · exact Companion.mass_finite k

theorem mass_positive (k : ℕ) (hk : 1≤k) (b : Bool) : 0<(mass k b).toReal := by
  cases b
  · rw [mass_real]
    change 0 < 2+(2:ℝ)/256^k
    positivity
  · exact Companion.mass_positive k hk

/-- A representative of any finite target, including either perturbation. -/
def bandTarget (k r : ℕ) (b : Bool) (w : S r) : S r :=
  (2:S r)^(2*k)*representative b+(2:S r)^(2*k+1)*w

theorem band_count (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) (b : Bool) (w : S r) :
    (TargetOne.count 6 (bandTarget k r b w):ℝ)=(mass k b).toReal*(den r:ℝ) := by
  rw [mass_real]
  have hne : (256:ℝ)^k ≠ 0 := by positivity
  cases b
  · rw [show bandTarget k r false w=target r (2*k) w by simp [bandTarget,representative,target]]
    simp only [Bool.false_eq_true,if_false]
    have h : (256:ℝ)^k*(TargetOne.count 6 (target r (2*k) w):ℝ)=
        (2*(256:ℝ)^k+2)*(den r:ℝ) := by exact_mod_cast count_positive k r hk hr w
    field_simp
    linarith
  · rw [show bandTarget k r true w=Companion.target r (2*k) w by simp [bandTarget,representative,Companion.target]]
    simp only [if_true]
    have h : (256:ℝ)^k*(TargetOne.count 6 (Companion.target r (2*k) w):ℝ)+2*(den r:ℝ)=
        2*(256:ℝ)^k*(den r:ℝ) := by exact_mod_cast Companion.count_band k r hk hr w
    field_simp
    linarith

theorem one_tube (k j : ℕ) (b : Bool) (t : S j) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers=1) (h : (TargetOne.count 6 t:ℝ)=(mass k b).toReal*(den j:ℝ)) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (RamField.cylinder j t)) =
      mass k b * lam (RamField.cylinder j t) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let _ : Fintype (R j) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let q := (2^j : ℕ)^2
  have hc (z : R j) : lam (RamTransport.residueCell inc (digit j) z) = 1/(q:ℝ≥0∞) := by
    change lam (RamField.cylinder j z) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol j z
  rw [show lam (RamField.cylinder j t) = 1/(q:ℝ≥0∞) from hc t]
  refine (RamTransport.fiber_count_to_tube inc inc_injective (digit j) lam
    (fun z => (open_cylinder j z).measurableSet) _ hc t).trans ?_
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (ENNReal.mul_ne_top (mass_finite k b) (by finiteness))).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_one,h]
  change (mass k b).toReal * ((q^5:ℕ):ℝ) * (1/(q:ℝ))^6 = _
  push_cast
  have hq : (q:ℝ) ≠ 0 := by dsimp [q]; positivity
  field_simp

private theorem child_ball (r : ℕ) (a : O) :
    ballAt r a = RamField.cylinder (r+1) (digit (r+1) a) ∪
      RamField.cylinder (r+1) (digit (r+1) a+center r*pi) := by
  have test (z : O) : (pi:O)^(2*r+1) ∣ z-a ↔
      digit (r+1) z=digit (r+1) a ∨ digit (r+1) z=digit (r+1) a+center r*pi := by
    rw [odd_dvd_iff,map_sub]
    exact childrenAt r _ _
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    rcases (test z).mp hz with h|h
    · exact Or.inl ⟨z,h,rfl⟩
    · exact Or.inr ⟨z,h,rfl⟩
  · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
    · exact ⟨z,(test z).mpr (Or.inl hz),rfl⟩
    · exact ⟨z,(test z).mpr (Or.inr hz),rfl⟩

private theorem two_tubes (k r : ℕ) (b : Bool) (a : O) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers=1)
    (h₁ : (TargetOne.count 6 (digit (r+1) a):ℝ)=(mass k b).toReal*(den (r+1):ℝ))
    (h₂ : (TargetOne.count 6 (digit (r+1) a+center r*pi):ℝ)=(mass k b).toReal*(den (r+1):ℝ)) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (ballAt r a)) =
      mass k b * lam (ballAt r a) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let s := digit (r+1) a
  let A := RamField.cylinder (r+1) s
  let B := RamField.cylinder (r+1) (s+center r*pi)
  let T := RamTransport.tube K integers
  let μ := Measure.pi fun _ : TargetOne.Idx => lam
  change μ (T (ballAt r a)) = mass k b * lam _
  have hdiff : s ≠ s+center r*pi := by
    intro h
    apply distinct r
    linear_combination h
  have hab : Disjoint A B := disjoint_cyl _ hdiff
  have hadd : T (A ∪ B) = T A ∪ T B := by
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
  rw [child_ball,hadd,measure_union hdis hmT,measure_union hab hmB,
    one_tube k _ b _ lam hvol h₁,one_tube k _ b _ lam hvol h₂,mul_add]

private theorem digit_target (k r : ℕ) (u : Oˣ) (w : O)
    (h : (u:O)=representative (bit u)+2*w) :
    digit r ((4:O)^k*(u:O)) = bandTarget k r (bit u) (digit r w) := by
  rw [h,map_mul,map_pow,map_ofNat,map_add,map_mul,map_ofNat,map_representative]
  unfold bandTarget
  rw [pow_succ (2:S r) (2*k),show (2:S r)^(2*k)=(4:S r)^k by rw [pow_mul]; congr 1; ring]
  ring

private theorem shifted_target (k r : ℕ) (hr : 2*k+1≤r) (b : Bool) (w : S (r+1)) :
    bandTarget k (r+1) b w+center r*pi =
      bandTarget k (r+1) b (w+(2:S (r+1))^(r-(2*k+1))*pi) := by
  have he : r=(2*k+1)+(r-(2*k+1)) := by omega
  simp only [bandTarget,center,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2:S (r+1))^r = 2^(2*k+1)*2^(r-(2*k+1)) by rw [← pow_add,← he]]
  ring

/-- Both unit classes stabilize at every later uniformizer depth. -/
theorem all_late (k d : ℕ) (hk : 1≤k) (hd : 4*k+2≤d) (u : Oˣ)
    (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers=1) :
    let B := precisionCell d ((4:O)^k*(u:O))
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      mass k (bit u) * lam B := by
  obtain ⟨w,hw⟩ := decomposition u
  rcases Nat.even_or_odd d with ⟨r,hr⟩|⟨r,hr⟩
  · rw [show d=2*r by omega]
    dsimp only
    rw [even_cell,digit_target k r u w hw]
    exact one_tube k r _ _ lam hvol (band_count k r hk (by omega) _ _)
  · rw [show d=2*r+1 by omega]
    change (Measure.pi fun _ : TargetOne.Idx => lam)
      (RamTransport.tube K integers (ballAt r ((4:O)^k*(u:O)))) = _
    apply two_tubes k r (bit u) _ lam hvol
    · rw [digit_target k (r+1) u w hw]
      exact band_count k (r+1) hk (by omega) _ _
    · rw [digit_target k (r+1) u w hw,shifted_target k r (by omega)]
      exact band_count k (r+1) hk (by omega) _ _

end RamDilate.UnitClass
#print axioms RamDilate.UnitClass.band_count
#print axioms RamDilate.UnitClass.all_late
