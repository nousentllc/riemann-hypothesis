import PrimitiveLift
import DyadicBase
import FourCounts
open Finset TargetOne
noncomputable section
namespace DyadicWave

theorem primitive_mod_eight (t : ℕ) : coarsePrim 6 ((4*t : ℕ) : ZMod 8)=30720 := by
  have hz := lift_primitive 0 6 0
  have hf := lift_primitive 0 6 4
  have ez := even_scaling 2 0
  have ef := even_scaling 2 1
  have hr0 : red 0 0=0 := map_zero _
  have hr4 : red 0 4=4 := map_ofNat _ _
  change count 6 (0:ZMod 8) = ev 6 (0:ZMod 8) + 1*coarsePrim 6 (red 0 0) at hz
  change count 6 (4:ZMod 8) = ev 6 (4:ZMod 8) + 1*coarsePrim 6 (red 0 4) at hf
  change ev 6 (0:ZMod 8)=64*count 6 (0:ZMod 2) at ez
  change ev 6 (4:ZMod 8)=64*count 6 (1:ZMod 2) at ef
  have z2 : count 6 (0:ZMod 2)=32 := by
    simpa only [show (4:ZMod 2)=0 by decide] using TargetFour.base_2
  rw [base_eight_zero,hr0,ez,z2] at hz
  rw [TargetFour.base_8,hr4,ef,small_2] at hf
  have h : ∀ a : ZMod 8, 4*a=0 ∨ 4*a=4 := by decide
  push_cast
  rcases h (t : ZMod 8) with h|h <;> rw [h] <;> omega

theorem step_counts (r t : ℕ) :
    16*count 6 ((4*t:ℕ):ZMod (2^(r+2))) =
      15*(2^(r+2))^5 + 1024*count 6 (t:ZMod (2^r)) := by
  rcases r with _ | k
  · have h1 : count 6 (t:ZMod 1)=1 := by
      rw [Subsingleton.elim (t:ZMod 1) 1,small_1]
    have h4 : ((4*t:ℕ):ZMod 4)=(4:ZMod 4) := by
      push_cast; rw [show (4:ZMod 4)=0 by decide,zero_mul]
    change 16*count 6 ((4*t:ℕ):ZMod 4)=15*4^5+1024*count 6 (t:ZMod 1)
    rw [h1,h4,TargetFour.base_4]; decide
  · have h := lift_primitive k 6 ((4*t:ℕ):ZMod (8*2^k))
    rw [map_natCast,primitive_mod_eight] at h
    have hmod : 8*2^k=4*2^(k+1) := by ring
    rw [hmod,even_scaling] at h
    rw [show 2^(k+1+2)=4*2^(k+1) by ring,h]
    ring

def normCount (r b : ℕ) : ℚ := (count 6 (b : ZMod (2^r)):ℚ) / (2^r:ℚ)^5
def density (k : ℕ) : ℚ := 1-1/(4*16^k)

theorem norm_step (r b : ℕ) :
    normCount (r+2) (4*b) = 15/16 + normCount r b /16 := by
  have h : (16:ℚ)*(count 6 ((4*b:ℕ):ZMod (2^(r+2))))=
      15*(2^(r+2):ℚ)^5+1024*count 6 (b:ZMod (2^r)) := by exact_mod_cast step_counts r b
  simp only [normCount,pow_add] at h ⊢
  field_simp
  linear_combination (norm := ring_nf) h

theorem density_step (k : ℕ) : density (k+1)=15/16+density k/16 := by
  simp only [density,pow_succ]; field_simp; ring

theorem all_depths (k r : ℕ) :
    normCount r (4^k) = if r < 2*k+2 then 1 else density k := by
  induction k generalizing r with
  | zero =>
    have h := count_all r
    simp only [pow_zero,Nat.mul_zero,Nat.zero_add,density,normCount,Nat.cast_one]
    by_cases hr : r<2
    · rw [if_pos hr] at h ⊢
      have H : (4:ℚ)*count 6 (1:ZMod (2^r)) = 4*(2^r:ℚ)^5 := by exact_mod_cast h
      field_simp; linarith
    · rw [if_neg hr] at h ⊢
      have H : (4:ℚ)*count 6 (1:ZMod (2^r)) = 3*(2^r:ℚ)^5 := by exact_mod_cast h
      field_simp; linarith
  | succ k ih =>
    rcases r with _|r
    · rw [if_pos (by omega)]
      have h : count 6 ((4^(k+1):ℕ):ZMod 1)=1 := by
        rw [Subsingleton.elim ((4^(k+1):ℕ):ZMod 1) 1,small_1]
      change (count 6 ((4^(k+1):ℕ):ZMod 1):ℚ)/1=1
      rw [h]; norm_num
    rcases r with _|r
    · rw [if_pos (by omega)]
      have hs : ((4^(k+1):ℕ):ZMod 2)=0 := by
        push_cast; rw [pow_succ,show (4:ZMod 2)=0 by decide,mul_zero]
      have h2 : count 6 (0:ZMod 2)=32 := by
        simpa only [show (4:ZMod 2)=0 by decide] using TargetFour.base_2
      norm_num [normCount,hs,h2]
    · rw [show 4^(k+1)=4*4^k by ring,norm_step,ih,density_step]
      split_ifs <;> first | omega | norm_num

theorem with_unit (k r u : ℕ) (hu : Odd u) :
    normCount r (4^k*u^2) = if r<2*k+2 then 1 else density k := by
  have h : IsUnit (u:ZMod (2^r)) := (ZMod.isUnit_iff_coprime ..).2
    ((Nat.coprime_two_right.2 hu).pow_right r)
  rw [←all_depths k r]
  unfold normCount
  congr 2
  push_cast
  rw [mul_comm]
  have hh := TargetFour.scaled h.unit ((4:ZMod (2^r))^k)
  simpa only [IsUnit.unit_spec] using hh

end DyadicWave
#print axioms DyadicWave.with_unit
