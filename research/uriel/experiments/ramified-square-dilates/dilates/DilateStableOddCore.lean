import DilateOddCellHaar

/-! Translate the two-child congruence to arbitrary centers and then multiply
by unit squares. No additional counting assumptions enter this step. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate.StableOdd
open OddCell RamField

theorem childrenAt (r : ℕ) (a s : S (r+1)) :
    pi^(2*r+1) ∣ s-a ↔ s=a ∨ s=a+center r*pi := by
  have h := children r (s-a+center r)
  rw [add_sub_cancel_right] at h
  constructor
  · intro hs
    rcases h.mp hs with hh|hh
    · left; linear_combination hh
    · right; linear_combination hh
  · rintro (hh|hh)
    · apply h.mpr; left; linear_combination hh
    · apply h.mpr; right; linear_combination hh

private theorem differ (r : ℕ) (a : S (r+1)) : a≠a+center r*pi := by
  intro h
  apply distinct r
  linear_combination h

theorem mixedAt (r : ℕ) (a : S (r+1)) :
    mixedCount r a = TargetOne.count 6 a + TargetOne.count 6 (a+center r*pi) := by
  classical
  let : Fintype (S (r+1)) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let targets : Finset (S (r+1)) := {a,a+center r*pi}
  have eq : mixedCount r a =
      Nat.card {x : Fin 6 → S (r+1) // TargetOne.sqSum x ∈ targets} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x
    change pi^(2*r+1) ∣ TargetOne.sqSum x - a ↔ TargetOne.sqSum x ∈ targets
    simpa only [targets,Finset.mem_insert,Finset.mem_singleton] using childrenAt r a (TargetOne.sqSum x)
  have hp := TargetFour.partitions (@TargetOne.sqSum (S (r+1)) _ 6) targets
  change _=∑ z ∈ targets, TargetOne.count 6 z at hp
  rw [eq,hp]
  have hnot : a ∉ ({a+center r*pi}:Finset (S (r+1))) := by
    simpa only [Finset.mem_singleton] using differ r a
  simp only [targets,Finset.sum_insert hnot,Finset.sum_singleton]

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
    (h : 256^k*TargetOne.count 6 t=(2*256^k+2)*den j) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (RamField.cylinder j t)) =
      (2+2/256^k:ℝ≥0∞)*lam (RamField.cylinder j t) := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id locally
  let _ : Fintype (R j) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  let q := (2^j : ℕ)^2
  have mass (z : R j) : lam (RamTransport.residueCell inc (digit j) z) = 1/(q:ℝ≥0∞) := by
    change lam (RamField.cylinder j z) = _
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using cyl_mass lam hvol j z
  have hc : lam (RamField.cylinder j t)=1/(q:ℝ≥0∞) := mass t
  rw [hc]
  have tube := RamTransport.fiber_count_to_tube inc inc_injective (digit j) lam
      (fun z => (open_cylinder j z).measurableSet) _ mass t
  refine tube.trans ?_
  have hn : (256:ℝ)^k * (TargetOne.count 6 t:ℝ) = (2*(256:ℝ)^k+2)*(q:ℝ)^5 := by
    change 256^k * TargetOne.count 6 t = (2*256^k+2)*q^5 at h
    exact_mod_cast h
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_add (a:=2) (b:=2/256^k) (by finiteness) (by finiteness),
    ENNReal.toReal_one,ENNReal.toReal_ofNat]
  have hq : (q:ℝ) ≠ 0 := by dsimp [q]; positivity
  field_simp
  linarith

/-- Two equal normalized child ratios imply the identical ratio for the
whole odd-depth cell, after any integral unit-square scaling. -/
theorem haar_pair (k r : ℕ) (a : O) (u : Oˣ) (lam : Measure K) [lam.IsAddHaarMeasure]
    (hvol : lam integers = 1)
    (h₁ : 256^k*TargetOne.count 6 (digit (r+1) a)=(2*256^k+2)*den (r+1))
    (h₂ : 256^k*TargetOne.count 6 (digit (r+1) a+center r*pi)=(2*256^k+2)*den (r+1)) :
    let B := ballAt r ((u:O)^2*a)
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers B) =
      (2+2/256^k:ℝ≥0∞)*lam B := by
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
  have hA : μ (T A)=(2+2/256^k:ℝ≥0∞)*lam A := one_tube k j _ lam hvol (by rw [TargetFour.scaled]; exact h₁)
  have hB : μ (T B)=(2+2/256^k:ℝ≥0∞)*lam B := one_tube k j _ lam hvol (by rw [TargetFour.scaled]; exact h₂)
  rw [hp,hTA,measure_union hdis hmT,measure_union hab hmB,hA,hB,mul_add]

end RamDilate.StableOdd
#print axioms RamDilate.StableOdd.haar_pair
