import FourBase
import FourEven
open TargetOne
namespace TargetFour
theorem total_all (r : ℕ) :
    64*count 6 (4:ZMod (2^r))=(if r<4 then 64 else 63)*(2^r)^5 := by
  rcases r with _|r
  · rw [show 2^0=1 by decide,base_1]; decide
  rcases r with _|r
  · rw [show 2^1=2 by decide,base_2]; decide
  rcases r with _|r
  · rw [show 2^2=4 by decide,base_4]; decide
  rcases r with _|r
  · rw [show 2^3=8 by decide,base_8]; decide
  rcases r with _|k
  · rw [show 2^4=16 by decide,base_16]; decide
  change 64*count 6 (4:ZMod (2^(k+5)))=(if k+5<4 then 64 else 63)*(2^(k+5))^5
  rw [if_neg (by omega),show 2^(k+5)=32*2^k by ring,orbit_count,base_32]
  ring

private theorem tiny_even (M : ℕ) [NeZero M] (hs : M≤2) (hz : (4:ZMod M)=0) : evenCount M=1 := by
  let F := {x : Fin 6 → ZMod M // sqSum x=4 ∧ allEven x}
  have h0 (x : F) : x.1=0 := by
    funext i; apply ZMod.val_injective
    have := (x.1 i).val_lt
    have := x.2.2 i
    change _=(0 : ZMod M).val
    rw [ZMod.val_zero]; omega
  haveI : Subsingleton F := ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
  haveI : Nonempty F := ⟨⟨0,by simp [sqSum,hz],by simp [allEven]⟩⟩
  exact Nat.card_unique (α := F)

theorem even_all (r : ℕ) : 64*evenCount (2^r)=
    (if r=0 then 64 else if r=1 then 2 else if r<4 then 4 else 3)*(2^r)^5 := by
  rcases r with _|r
  · rw [show 2^0=1 by decide,tiny_even 1 (by decide) (by decide)]; decide
  rcases r with _|k
  · rw [show 2^1=2 by decide,tiny_even 2 (by decide) (by decide)]; decide
  change 64*evenCount (2^(k+2))=(if k+2=0 then 64 else if k+2=1 then 2 else if k+2<4 then 4 else 3)*(2^(k+2))^5
  rw [if_neg (by omega),if_neg (by omega),show 2^(k+2)=4*2^k by ring,even_scaling]
  have h := TargetOne.count_all k
  by_cases hk : k<2
  · rw [if_pos hk] at h
    rw [if_pos (by omega)]
    linear_combination (norm := ring_nf) 1024*h
  · rw [if_neg hk] at h
    rw [if_neg (by omega)]
    linear_combination (norm := ring_nf) 1024*h

theorem primitive_all (r : ℕ) : 64*primCount (2^r) =
    (if r=0 then 0 else if r=1 then 62 else 60)*(2^r)^5 := by
  have ht := total_all r
  rw [split_count,Nat.mul_add] at ht
  have he := even_all r
  split_ifs at ht he ⊢ <;> omega
end TargetFour
#print axioms TargetFour.primitive_all
#print axioms TargetFour.even_all
#print axioms TargetFour.total_all
