import OverlapVolume

open RamField FourChart RamDilate.StableOdd RamDilate.OddCell
noncomputable section
namespace PivotOverlap

def orderEquiv : O ≃+* D := RingEquiv.ofBijective inc.rangeRestrict
  ⟨fun _ _ h => inc_injective (congrArg Subtype.val h), inc.rangeRestrict_surjective⟩
def fold (x : O) : O := x+x^2

theorem child_image (e b : O) : ∃ u : O, fold (e+2*u)=fold e+2*b := by
  obtain ⟨v,hv⟩ := poly_onto (orderEquiv e) 1 (orderEquiv b)
  refine ⟨orderEquiv.symm v,orderEquiv.injective ?_⟩
  simp only [fold,map_add,map_mul,map_pow,map_ofNat,RingEquiv.apply_symm_apply]
  unfold poly errorTerm at hv
  linear_combination 2*hv

theorem even_difference {x a : O} (h : digit 1 x=digit 1 a) : ∃ u : O, x=a+2*u := by
  have hm : inc x ∈ precisionCell (2*1) a := by
    rw [even_cell]; exact ⟨x,h,rfl⟩
  obtain ⟨w,hw,hh⟩ := hm
  have eq := inc_injective hh
  subst w
  have hp : (pi:O)^(2*1)=(2:O) := pi_sq
  change (pi:O)^(2*1) ∣ x-a at hw
  rw [hp] at hw
  obtain ⟨u,hu⟩ := hw
  exact ⟨u,by linear_combination hu⟩

theorem digit_fold (x : R 1) : x+x^2 = (⟨0,x.im⟩ : R 1) := by
  obtain ⟨a,b⟩ := x
  fin_cases a <;> fin_cases b <;> decide

theorem image_digit (t : O) : (∃ v, fold v=t) ↔ (digit 1 t).re=0 := by
  constructor
  · rintro ⟨v,rfl⟩
    rw [fold,map_add,map_pow,digit_fold]
  · intro h
    have hh : digit 1 t=digit 1 (fold t) := by
      rw [fold,map_add,map_pow,digit_fold]
      exact QuadraticAlgebra.ext h rfl
    obtain ⟨b,hb⟩ := even_difference hh
    obtain ⟨u,hu⟩ := child_image t b
    exact ⟨t+2*u,hu.trans hb.symm⟩

theorem pi_condition (t : O) : (pi:O) ∣ t ↔ (digit 1 t).re=0 := by
  have h := odd_dvd_iff 0 t
  simp only [Nat.mul_zero,zero_add,pow_one] at h
  rw [h]
  constructor
  · rintro ⟨x,hx⟩
    rw [hx]; simp [pi,QuadraticAlgebra.re_mul,show (2:ZMod (2^(0+1)))=0 by decide]
  · intro hs
    refine ⟨⟨(digit 1 t).im,0⟩,?_⟩
    apply QuadraticAlgebra.ext
    · simp [pi,hs]
    · simp [pi]

theorem root_pair (v : O) : fold (-1-v)=fold v ∧ v≠ -1-v := by
  constructor
  · unfold fold; ring
  · intro he
    have h2 : (2:O)*v= -1 := by linear_combination he
    have hv := congrArg (digit 1) h2
    rw [map_mul,map_ofNat,map_neg,map_one] at hv
    have hz : (2:R 1)=0 := by decide
    rw [hz,zero_mul] at hv
    exact (by decide : (0:R 1) ≠ -1) hv

theorem exactly_two (t : O) :
    (pi:O) ∣ t ↔ ∃ v : O, v≠ -1-v ∧ ∀ x : O, fold x=t ↔ x=v ∨ x= -1-v := by
  rw [pi_condition,←image_digit]
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨v,(root_pair v).2,fun x => ?_⟩
    constructor
    · intro h
      have he := congrArg inc h
      simp only [fold,map_add,map_pow] at he
      rcases (fold_iff _ _).mp he with he|he
      · exact Or.inl (inc_injective he)
      · right; apply inc_injective; simpa using he
    · rintro (rfl|rfl)
      · rfl
      · exact (root_pair _).1
  · rintro ⟨v,_,h⟩
    exact ⟨v,(h v).mpr (Or.inl rfl)⟩

end PivotOverlap
#print axioms PivotOverlap.child_image
#print axioms PivotOverlap.image_digit
#print axioms PivotOverlap.pi_condition
#print axioms PivotOverlap.exactly_two
