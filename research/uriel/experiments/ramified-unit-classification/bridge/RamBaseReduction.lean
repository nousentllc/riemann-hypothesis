import RamBaseFive
namespace RamBase.Five
open Finset

/-- The π^5 reduction of the common contact ring, with the invariant factors
8 and 4 in this order. -/
def reduce : R →+ D where
  toFun z := (ZMod.castHom (by decide : 8∣32) _ z.re, ZMod.castHom (by decide : 4∣32) _ z.im)
  map_zero' := by simp
  map_add' x y := by simp [Prod.add_def]

def pi32 : R := ⟨0,1⟩
theorem pi32_square : pi32^2=2 := by decide +kernel

private def preimage (z : R) : R := ⟨(z.im.val/4 : ℕ), (z.re.val/8 : ℕ)⟩
private theorem reduction_check : RamBase.checks (fun j => decide (
    reduce ((decode j)^2) = square (reduce (decode j)) ∧
    reduce (pi32^5 * decode j) = 0 ∧
    (reduce (decode j) = 0 → pi32^5 * preimage (decode j) = decode j))) 1024 = true := by
  decide +kernel

private theorem facts (z : R) :
    reduce (z^2) = square (reduce z) ∧ reduce (pi32^5*z)=0 ∧
      (reduce z=0 → pi32^5*preimage z=z) := by
  simpa only [decode_encode] using
    of_decide_eq_true (RamBase.select reduction_check (encode z) (encode_lt z))

theorem reduce_surjective : Function.Surjective reduce := by
  intro z
  refine ⟨⟨(z.1.val : ZMod 32), (z.2.val : ZMod 32)⟩,?_⟩
  apply Prod.ext
  · change ZMod.castHom (by decide : 8∣32) _ (z.1.val : ZMod 32) = z.1
    rw [map_natCast,ZMod.natCast_zmod_val]
  · change ZMod.castHom (by decide : 4∣32) _ (z.2.val : ZMod 32) = z.2
    rw [map_natCast,ZMod.natCast_zmod_val]

theorem reduce_zero_iff (z : R) : reduce z = 0 ↔ ∃ w : R, z=pi32^5*w := by
  constructor
  · intro h; exact ⟨preimage z,((facts z).2.2 h).symm⟩
  · rintro ⟨w,rfl⟩; exact (facts w).2.1

theorem reduce_sqSum {d : ℕ} (x : Fin d → R) :
    reduce (TargetOne.sqSum x) = ∑ i, square (reduce (x i)) := by
  simp only [TargetOne.sqSum,map_sum,fun z => (facts z).1]
end RamBase.Five
#print axioms RamBase.Five.reduce_zero_iff
#print axioms RamBase.Five.reduce_sqSum
