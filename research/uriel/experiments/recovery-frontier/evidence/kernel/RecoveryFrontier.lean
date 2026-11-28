import Mathlib

namespace RecoveryFrontier

/-- No retained edge can have a step with image outside the support differences. -/
theorem no_edge_of_missing_difference {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (phi : A →+ B) (tops : Finset A) (support : Set B) (h : A)
    (contained : ∀ t ∈ tops, phi t ∈ support)
    (missing : ∀ u ∈ support, ∀ v ∈ support, v - u ≠ phi h)
    {t : A} (ht : t ∈ tops) : t + h ∉ tops := by
  intro hit
  apply missing (phi t) (contained t ht) (phi (t+h)) (contained (t+h) hit)
  rw [map_add]
  abel

/-- A weighted loss supported on exceptional directions costs at most their weight plus errors. -/
theorem weighted_loss {I : Type*} (indices : Finset I) (w k r err flag : I → ℝ)
    (nonneg : ∀ i ∈ indices, 0 ≤ w i)
    (localBound : ∀ i ∈ indices, k i - r i ≤ flag i + err i) :
    (∑ i ∈ indices, w i * k i) - (∑ i ∈ indices, w i * r i) ≤
      (∑ i ∈ indices, w i * flag i) + (∑ i ∈ indices, w i * err i) := by
  have h := Finset.sum_le_sum (s := indices)
    (fun i hi => mul_le_mul_of_nonneg_left (localBound i hi) (nonneg i hi))
  simpa only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] using h

/-- Recover the fraction from a two-sided normalized gap and a positive allowance. -/
theorem fraction_interval (k r exceptional error : ℝ) (positive : 0 < k)
    (lower : -error ≤ k-r) (upper : k-r ≤ exceptional+error) :
    1 - (exceptional + error) / k ≤ r / k ∧ r / k ≤ 1 + error / k := by
  constructor
  · apply (le_div_iff₀ positive).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ positive.ne']
    linarith
  · apply (div_le_iff₀ positive).2
    rw [add_mul, one_mul, div_mul_cancel₀ _ positive.ne']
    linarith

#print axioms no_edge_of_missing_difference
#print axioms weighted_loss
#print axioms fraction_interval
end RecoveryFrontier
