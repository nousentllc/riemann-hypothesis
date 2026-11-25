import Mathlib

namespace ProgressionGeometry

/-- An affine progression with starting point no larger than its increment meets
every forward interval of length that increment, including the initial interval. -/
theorem bounded_wait (n d k : ℕ) (hd : 0 < d) (hn : n ≤ d) :
    ∃ j : ℕ, k < n + d*j ∧ n + d*j ≤ k+d := by
  by_cases hk : k < n
  · exact ⟨0, by simpa, by simp; omega⟩
  let t := k - n
  have hr := Nat.mod_lt t hd
  have hdiv := Nat.mod_add_div t d
  have ht : t + n = k := Nat.sub_add_cancel (by omega)
  refine ⟨t/d + 1, ?_, ?_⟩ <;> rw [Nat.mul_add, Nat.mul_one] <;> omega

/-- For cutoffs equal to progression points the forward delay is exactly d. -/
theorem sharp_at_member (n d i j : ℕ) (h : n+d*i < n+d*j) :
    n+d*i+d ≤ n+d*j := by
  have hi : i < j := by
    by_contra! hc
    exact (not_le_of_gt h) (Nat.add_le_add_left (Nat.mul_le_mul_left d hc) n)
  calc n+d*i+d = n+d*(i+1) := by ring
       _ ≤ n+d*j := Nat.add_le_add_left (Nat.mul_le_mul_left d hi) n

/-- All good indices below a cutoff, expressed without a search. -/
theorem cutoff_indices (n d k j : ℕ) (hd : 0 < d) (h : n ≤ k) :
    n + d*j ≤ k ↔ j ≤ (k-n)/d := by
  rw [Nat.le_div_iff_mul_le hd, Nat.mul_comm j d]
  omega

/-- A bound proved on N(1+Qj) immediately yields the original lower estimate
within NQ of each specified cutoff. The predicate may include all original
fiber and dilation data. -/
theorem from_progression {P : ℕ → Prop} {N Q : ℕ} (hQ : 0 < Q) (hN : 0 < N)
    (hP : ∀ j, P (N*(1+Q*j))) (k : ℕ) :
    ∃ a : ℕ, k < a ∧ a ≤ k+N*Q ∧ P a := by
  have hn : N ≤ N*Q := by simpa using Nat.mul_le_mul_left N hQ
  obtain ⟨j,hl,hu⟩ := bounded_wait N (N*Q) k (Nat.mul_pos hN hQ) hn
  have he : N*(1+Q*j) = N+(N*Q)*j := by ring
  exact ⟨_, hl, hu, he ▸ hP j⟩

end ProgressionGeometry
#print axioms ProgressionGeometry.from_progression
#print axioms ProgressionGeometry.sharp_at_member
#print axioms ProgressionGeometry.cutoff_indices
