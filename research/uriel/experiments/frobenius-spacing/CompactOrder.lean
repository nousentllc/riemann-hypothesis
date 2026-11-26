import Lib.General.NumberTheory.QuadFieldSplitting
import SpacingLogic

namespace FrobeniusSpacing

/-- Calls the pinned compact proof's exact dyadic valuation lemma. -/
theorem compact_order_guard {s p i : ℕ} (hp : 1 < p) (hi : 0 < i)
    (hsize : (p + 1) * i < 2 ^ s) :
    ((-(p : ℤ) : ℤ) : ZMod (2 ^ (s + 1))) ^ i ≠ 1 := by
  intro he
  have h := two_pow_le_of_pow_eq_one (q := -(p : ℤ)) (by simpa using hp) hi he
  exact hsize.not_ge (by simpa using h)

/-- Join the spacing implication to the compact source's arithmetic guard.
    The place projection and the size bound are explicit inputs. -/
theorem compact_no_two_short_targets {G : Type*} [CommGroup G]
    {s p i j : ℕ} (cl : G →* (ZMod (2 ^ (s + 1)))ˣ)
    {T : Set G} {g t : G} (hp : 1 < p) (hi : 0 < i) (hij : i < j) (hjs : j < s)
    (hsize : (p + 1) * s < 2 ^ s)
    (hg : (cl g : ZMod (2 ^ (s + 1))) = ((-(p : ℤ) : ℤ) : ZMod (2 ^ (s + 1))))
    (ht : t ∈ T) (hTi : g ^ i * t ∈ T) (hTj : g ^ j * t ∈ T)
    (spacing : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T,
      0 < i → i < j → cl (b / a) ^ j = cl (c / a) ^ i → cl (b / a) = 1) :
    False := by
  refine two_targets_conflict cl hi hij ht hTi hTj spacing ?_
  intro he
  have he' := congrArg (fun z : (ZMod (2 ^ (s + 1)))ˣ => (z : ZMod (2 ^ (s + 1)))) he
  have hsmall : (p + 1) * i < 2 ^ s :=
    (Nat.mul_le_mul_left (p + 1) (hij.trans hjs).le).trans_lt hsize
  exact compact_order_guard hp hi hsmall (by simpa [hg] using he')

end FrobeniusSpacing

#print axioms FrobeniusSpacing.compact_order_guard
#print axioms FrobeniusSpacing.compact_no_two_short_targets
