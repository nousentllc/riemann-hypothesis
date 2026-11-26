import Mathlib

namespace FrobeniusSpacing

/-- A two-target collision would give the same mixed power on both sides.
    The order test removes the only configuration allowed by the spacing law. -/
theorem two_targets_conflict {G U : Type*} [CommGroup G] [CommGroup U]
    (cl : G →* U) {T : Set G} {g t : G} {i j : ℕ} (hi : 0 < i) (hij : i < j)
    (ht : t ∈ T) (hTi : g ^ i * t ∈ T) (hTj : g ^ j * t ∈ T)
    (spacing : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T,
      0 < i → i < j → cl (b / a) ^ j = cl (c / a) ^ i → cl (b / a) = 1)
    (orderTest : cl g ^ i ≠ 1) : False := by
  have hm : cl (g ^ i * t / t) ^ j = cl (g ^ j * t / t) ^ i := by
    simp only [mul_div_cancel_right, map_pow, ← pow_mul]
    rw [Nat.mul_comm i j]
  exact orderTest (by simpa using spacing t ht (g ^ i * t) hTi (g ^ j * t) hTj hi hij hm)

/-- If either guard is absent, the mixed-power identity itself still holds. -/
theorem mixed_power {U : Type*} [Monoid U] (g : U) (i j : ℕ) :
    (g ^ i) ^ j = (g ^ j) ^ i := by rw [← pow_mul, ← pow_mul, Nat.mul_comm i j]

/-- An odd-displacement relation can have two different targets in one even cycle. -/
theorem two_odd_targets :
    (15 + 3) % 16 = 2 ∧ (15 + 7) % 16 = 6 ∧ Odd (3 : ℕ) ∧ Odd (7 : ℕ) := by decide

/-- In a dyadic quotient an odd power can be identity only for identity itself.
    This is an alternative check of the guard for odd candidates. -/
theorem odd_power_order_guard {U : Type*} [Group U] (g : U) (s i : ℕ)
    (hs : orderOf g ∣ 2 ^ s) (hi : Odd i) (hg : g ≠ 1) : g ^ i ≠ 1 := by
  intro h
  have hc : Nat.Coprime (2 ^ s) i := hi.coprime_two_left.pow_left s
  have hd := orderOf_dvd_iff_pow_eq_one.mpr h
  exact hg (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc hs hd))

/-- The two modular displacements of the finite witness satisfy the mixed
    power equation with a nonidentity first displacement. -/
theorem dyadic_collision_certificate :
    (51 : ZMod 64) ^ 3 = 43 ∧ (51 : ZMod 64) ^ 7 = 27 ∧
    (43 : ZMod 64) ^ 7 = (27 : ZMod 64) ^ 3 ∧
    (43 : ZMod 64) ≠ 1 ∧ (51 : ZMod 64) ^ 8 ≠ 1 ∧
    (51 : ZMod 64) ^ 16 = 1 := by decide

end FrobeniusSpacing

#print axioms FrobeniusSpacing.two_targets_conflict
#print axioms FrobeniusSpacing.mixed_power
#print axioms FrobeniusSpacing.two_odd_targets
#print axioms FrobeniusSpacing.odd_power_order_guard
#print axioms FrobeniusSpacing.dyadic_collision_certificate
