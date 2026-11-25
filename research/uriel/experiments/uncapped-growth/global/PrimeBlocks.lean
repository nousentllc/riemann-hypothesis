import Mathlib

open scoped BigOperators
noncomputable section

namespace PrimeBlocks

/-- A floor eventually in k is a floor at all k if every finite shell is positive. -/
theorem tail_iff (f : ℕ → ℝ) (hpos : ∀ k, 0 < f k) :
    (∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ f k) ↔
    (∃ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ k ≥ K, c ≤ f k) := by
  constructor
  · rintro ⟨c,hc,h⟩
    exact ⟨0,c,hc,fun k _ => h k⟩
  · rintro ⟨K,c,hc,h⟩
    induction K generalizing c with
    | zero => exact ⟨c,hc,fun k => h k (Nat.zero_le _)⟩
    | succ K ih =>
      refine ih (min c (f K)) (lt_min hc (hpos K)) ?_
      intro k hk
      by_cases he : k = K
      · subst k; exact min_le_right _ _
      · exact (min_le_left _ _).trans (h k (by omega))

/-- Every block is a rational prime. A product over independent integer-valuations
has a positive floor exactly when each block sequence has a positive tail floor. -/
theorem block_criterion (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (f : ℕ → ℕ → ℝ)
    (hpos : ∀ p ∈ P, ∀ k, 0 < f p k) :
    (∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 0 < t → c ≤ ∏ p ∈ P, f p (t.factorization p)) ↔
    ∀ p ∈ P, ∃ K : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ k ≥ K, d ≤ f p k := by
  classical
  constructor
  · rintro ⟨c,hc,h⟩ p hp
    apply (tail_iff _ (hpos p hp)).mp
    let A := ∏ q ∈ P.erase p, f q 0
    have hA : 0 < A := Finset.prod_pos fun q hq => hpos q (Finset.mem_of_mem_erase hq) _
    refine ⟨c/A, div_pos hc hA, fun k => (div_le_iff₀ hA).2 ?_⟩
    have hh := h (p^k) (pow_pos (hP p hp).pos _)
    rw [← Finset.mul_prod_erase _ _ hp] at hh
    have hx : (p^k).factorization p = k := by simp [(hP p hp).factorization]
    rw [hx] at hh
    refine hh.trans_eq (congrArg (f p k * ·) (Finset.prod_congr rfl ?_))
    intro q hq
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    obtain ⟨-,hqP⟩ := Finset.mem_erase.mp hq
    have hnd : ¬ q ∣ p ^ k := fun hdiv => hqp ((Nat.dvd_prime_two_le (hP p hp) (hP q hqP).two_le).1 ((hP q hqP).dvd_of_dvd_pow hdiv))
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
  · intro h
    have floors : ∀ p : ℕ, ∃ d : ℝ, 0 < d ∧ (p ∈ P → ∀ k, d ≤ f p k) := by
      intro p
      by_cases hp : p ∈ P
      · obtain ⟨d,hd,hh⟩ := (tail_iff _ (hpos p hp)).mpr (h p hp)
        exact ⟨d,hd,fun _ => hh⟩
      · exact ⟨1,zero_lt_one,fun h => (hp h).elim⟩
    choose d hd hle using floors
    exact ⟨∏ p ∈ P, d p, Finset.prod_pos (fun p _ => hd p),
      fun t _ => Finset.prod_le_prod (fun p _ => (hd p).le) (fun p hp => hle p hp _)⟩

end PrimeBlocks
#print axioms PrimeBlocks.tail_iff
#print axioms PrimeBlocks.block_criterion
