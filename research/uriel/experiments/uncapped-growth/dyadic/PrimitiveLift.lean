import OddSquares
import EvenDescent
open Finset TargetOne
noncomputable section
namespace DyadicWave

-- First odd coordinate: odd head and arbitrary tail, or even head and primitive tail.
def coarsePrim : ℕ → ZMod 8 → ℕ
  | 0,_ => 0
  | d+1,b => 4*count d (b-1) + ∑ a : ZMod 8, if a.val%2=0 then coarsePrim d (b-a^2) else 0

theorem parity_red (k : ℕ) (x : ZMod (8*2^k)) : (red k x).val%2=x.val%2 := by
  have h := congrArg (red k) (ZMod.natCast_zmod_val x)
  simp only [map_natCast] at h
  rw [←h,ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]

theorem lift_primitive (k d : ℕ) (b : ZMod (8*2^k)) :
    count d b = ev d b + (2^k)^(d-1)*coarsePrim d (red k b) := by
  classical
  induction d generalizing b with
  | zero => simp [coarsePrim,ev_zero]
  | succ d ih =>
    have oddtest : ∀ a : ZMod 8, a^2=1 ↔ ¬a.val%2=0 := by decide
    have separate (x : ZMod (8*2^k)) : count d (b-x^2) =
        (if (red k x)^2=1 then count d (b-x^2) else 0) +
        ((if x.val%2=0 then ev d (b-x^2) else 0) +
         (if (red k x).val%2=0 then (2^k)^(d-1)*coarsePrim d (red k b-(red k x)^2) else 0)) := by
      simp only [oddtest,parity_red]
      by_cases h : x.val%2=0 <;> simp [h]
      have H := ih (b-x^2)
      have hm : red k (b-x^2) = red k b-(red k x)^2 :=
        ((red k).map_sub b (x^2)).trans (congrArg (fun z => red k b-z) ((red k).map_pow x 2))
      rw [hm] at H
      exact H
    have hscale : (∑ x : ZMod (8*2^k), if (red k x).val%2=0 then
        (2^k)^(d-1)*coarsePrim d (red k b-(red k x)^2) else 0) =
        (2^k)^d * ∑ a : ZMod 8, if a.val%2=0 then coarsePrim d (red k b-a^2) else 0 := by
      rw [reduceSum k (fun a => if a.val%2=0 then (2^k)^(d-1)*coarsePrim d (red k b-a^2) else 0)]
      rcases d with _ | d
      · simp [coarsePrim]
      · simp only [Nat.add_one_sub_one,pow_succ]
        simp only [←mul_ite_zero,←Finset.mul_sum]; ring
    rw [count_succ,Finset.sum_congr rfl (fun x _ => separate x),Finset.sum_add_distrib,
      Finset.sum_add_distrib,oddTail,←ev_succ,hscale,coarsePrim,Nat.add_one_sub_one]
    ring

end DyadicWave
#print axioms DyadicWave.lift_primitive
