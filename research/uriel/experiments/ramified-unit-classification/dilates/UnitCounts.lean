import UnitLow
import CompanionCounts
import DilateEndpoint

/-! The entire positive residue cylinder, with arbitrary perturbations at all later depths. -/
noncomputable section
namespace RamDilate.UnitClass
open TargetOne

/-- The targets in the class of the square branch, before choosing a unit lift. -/
def target (r j : ℕ) (w : S r) : S r := (2:S r)^j+(2:S r)^(j+1)*w

theorem target_zero (r : ℕ) (w : S r) : target r 0 w = 1+2*w := by simp [target]

theorem target_one (r : ℕ) (w : S r) : target r 1 w = 2+4*w := by
  unfold target
  ring

private def truncate (r : ℕ) (w : S (r+1)) : S r := RamLift.reduce (2^r) 2 w

private theorem down (r j : ℕ) (w : S (r+1)) :
    imprim (r+1) (target (r+1) (j+1) w) =
      64*count 6 (target r j (truncate r w)) := by
  rw [show target (r+1) (j+1) w = 2*target (r+1) j w by unfold target; ring]
  have h := Descent.double_count (n := 2^r) (target (r+1) j w)
  let f : S (r+1) →+* S r := RamLift.reduce (2^r) 2
  have e : f (target (r+1) j w) = target r j (truncate r w) := by
    simp only [target,map_add,map_mul,map_pow,map_ofNat]
    rfl
  rw [show RamLift.reduce (2^r) 2 (target (r+1) j w) = _ from e] at h
  exact h

private theorem one_imprim (r : ℕ) (hr : 1≤r) (w : S r) :
    imprim r (1+2*w) = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  revert w
  unfold imprim allEven S RamField.R
  rw [show 2^(1+k)=2*2^k by ring]
  intro w
  let f := RamLift.reduce 2 (2^k)
  have : IsEmpty {x : Fin 6 → RamLift.B (2*2^k) //
      sqSum x = 1+2*w ∧ ∀ i,(x i).re.val%2=0} := ⟨fun x => by
    have hz (i : Fin 6) : (f (x.val i))^2=0 := by
      have hre : (f (x.val i)).re=0 := by
        change TargetFour.reduce 2 (2^k) (x.val i).re=0
        rw [← ZMod.natCast_zmod_val ((x.val i).re),map_natCast]
        apply ZMod.val_injective
        rw [ZMod.val_natCast]
        exact x.property.2 i
      have h₂ : (2:ZMod 2)=0 := by decide +kernel
      apply QuadraticAlgebra.ext <;>
        simp [pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hre,h₂]
    have h := congrArg f x.property.1
    simp only [sqSum,map_sum,map_pow,map_add,map_one,map_mul,map_ofNat,hz,Finset.sum_const_zero] at h
    rw [show (2:RamLift.B 2)=0 by decide +kernel,zero_mul,add_zero] at h
    exact zero_ne_one h⟩
  exact Nat.card_of_isEmpty

private theorem prim_family (a v c r : ℕ) (hr : 3≤r)
    (h : ∀ b : S 3, prim 3 ((a:S 3)+(v:S 3)*b)=c*den 3) (b : S r) :
    prim r ((a:S r)+(v:S r)*b)=c*den r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [PrimitiveRing.card_eq] at h ⊢
  revert b
  unfold den S RamField.R
  rw [show 2^(3+k)=8*2^k by ring]
  intro b
  rw [CompanionPrimitive.lift,map_add,map_mul,map_natCast,map_natCast]
  change ∀ b : RamLift.B 8,
    PrimitiveRing.C 8 ((a:RamLift.B 8)+(v:RamLift.B 8)*b)=c*((8:ℕ)^2)^5 at h
  rw [h]
  ring

private theorem one_density (r : ℕ) (hr : 2≤r) (w : S r) :
    count 6 (target r 0 w) = 2*den r := by
  by_cases h : 3≤r
  · rw [target_zero, split, one_imprim r (by omega),zero_add]
    have hprim := prim_family 1 2 2 r h (by
      intro b
      have e := split 3 (1+2*b)
      rw [one_imprim 3 (by decide),zero_add,low3_one] at e
      change prim 3 (1+2*b) = _
      rw [← e]
      decide +kernel) w
    simpa only [Nat.cast_one,Nat.cast_ofNat] using hprim
  · obtain rfl : r=2 := by omega
    rw [target_zero,low2_one]
    decide +kernel

private theorem two_primitive (r : ℕ) (hr : 3≤r) (w : S r) :
    prim r (target r 1 w) = 2*den r := by
  rw [target_one]
  apply prim_family 2 4 2 r hr
  intro w
  have h := split 3 (target 3 1 w)
  rw [down 2 0 w,one_density 2 (by decide),target_one,low3_two] at h
  change prim 3 (2+4*w) = 2*1073741824
  change 2281701376 = 64*(2*1048576)+prim 3 (2+4*w) at h
  omega

private theorem prim_shift (r : ℕ) (hr : 3≤r) (a b : S r) :
    prim r (a+8*b)=prim r a := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [PrimitiveRing.card_eq]
  revert a b
  unfold S RamField.R
  rw [show 2^(3+k)=8*2^k by ring]
  intro a b
  exact (CompanionPrimitive.constant k a b).symm

private theorem finer (j r : ℕ) (hr : j+2≤r) (w : S r) :
    count 6 (target r j w) = count 6 (target r j 0) := by
  induction j generalizing r with
  | zero => rw [one_density r hr w,one_density r hr 0]
  | succ j ih =>
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    change count 6 (target (s+1) (j+1) w)=count 6 (target (s+1) (j+1) 0)
    have e := ih s (by omega) (truncate s w)
    have hz : truncate s (0:S (s+1)) = 0 := map_zero _
    have hp : prim (s+1) (target (s+1) (j+1) w)=prim (s+1) (target (s+1) (j+1) 0) := by
      by_cases hj : j=0
      · subst j
        rw [two_primitive _ (by omega),two_primitive _ (by omega)]
      · obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le (by omega : 1≤j)
        have h : target (s+1) (j+1) w = target (s+1) (j+1) 0+8*(2^t*w) := by
          rw [ht]
          unfold target
          ring
        rw [h,prim_shift _ (by omega)]
    rw [split _ (target (s+1) (j+1) w),split _ (target (s+1) (j+1) 0),down,down,hz,e,hp]

private theorem pow_zero (r : ℕ) : (2:S r)^r=0 := by
  have h : (2:ZMod (2^r))^r = 0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^r)
  simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (ZMod (2^r)) (S r)) h

/-- The positive count is uniform under an arbitrary shift within the first resolved cylinder. -/
theorem same_as_square (j r : ℕ) (hr : j+1≤r) (w : S r) :
    count 6 (target r j w)=count 6 ((2:S r)^j) := by
  have h0 : target r j 0 = (2:S r)^j := by simp [target]
  by_cases h : j+2≤r
  · rw [finer j r h w,h0]
  · obtain rfl : r=j+1 := by omega
    unfold target
    rw [pow_zero,zero_mul,add_zero]

theorem count_positive (k r : ℕ) (hk : 1≤k) (hr : 2*k+1≤r) (w : S r) :
    256^k * count 6 (target r (2*k) w) = (2*256^k+2)*den r := by
  rw [same_as_square _ _ hr, pow_mul, show (2:S r)^2=4 by ring]
  have h : r=(r-(2*k+1))+(2*k+1) := by omega
  revert w
  rw [h]
  intro _
  exact counts k hk _

end RamDilate.UnitClass
#print axioms RamDilate.UnitClass.same_as_square
#print axioms RamDilate.UnitClass.count_positive
