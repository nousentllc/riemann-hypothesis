import Mathlib

open scoped BigOperators
namespace BlockIdentification

/-- Every list of depths at distinct rational primes occurs for one multiplier. -/
theorem realize_shells (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) (k : ℕ → ℕ) :
    let t := ∏ q ∈ P, q^(k q)
    0 < t ∧ ∀ p ∈ P, t.factorization p = k p := by
  classical
  dsimp only
  refine ⟨Finset.prod_pos fun q hq => pow_pos (hp q hq).pos _, ?_⟩
  intro p hpP
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (hp q hq).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single p]
  · simp [(hp p hpP).factorization]
  · intro q hq hne
    simp [(hp q hq).factorization, hne]
  · exact fun h => (h hpP).elim

/-- Compensation cannot hide a collapsing component once all its companions have
uniform upper bounds. No individual upper bound is an assumption of the main equivalence. -/
theorem individual_of_product {V : Type} [DecidableEq V] (S : Finset V) (i : V) (hi : i ∈ S)
    (f : V → ℕ → ℝ) (U : V → ℝ) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v ∈ S, ∀ k, 0 ≤ f v k) (hU : ∀ v ∈ S.erase i, 0 < U v)
    (hle : ∀ v ∈ S.erase i, ∀ k, f v k ≤ U v)
    (hf : ∀ k, c ≤ ∏ v ∈ S, f v k) :
    ∃ d : ℝ, 0 < d ∧ ∀ k, d ≤ f i k := by
  let A := ∏ v ∈ S.erase i, U v
  have ha : 0 < A := Finset.prod_pos hU
  refine ⟨c/A,div_pos hc ha,fun k => (div_le_iff₀ ha).mpr ?_⟩
  have h := hf k
  rw [← Finset.mul_prod_erase _ _ hi] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (hpos _ hi _))
  exact Finset.prod_le_prod (fun v hv => hpos v (Finset.mem_of_mem_erase hv) k) (fun v hv => hle v hv k)
end BlockIdentification
#print axioms BlockIdentification.realize_shells
#print axioms BlockIdentification.individual_of_product
