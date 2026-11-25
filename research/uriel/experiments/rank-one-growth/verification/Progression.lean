import Inputs

open NumberField IsDedekindDomain Filter Topology
open GlobalTheory.CompanionTheory.SW

namespace DensityReplay

/-- On every row of a family: fixed positive exceptional factors, summably small
good-place errors. The lower constant is chosen before the row. -/
theorem uniform_product {F : Type} [Field F] [NumberField F]
    (B : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ℕ → HeightOneSpectrum (𝓞 F) → ℝ)
    (hbad : ∀ j v, v ∈ B → u j v = u 0 v)
    (hpos : ∀ v ∈ B, 0 < u 0 v)
    (hgood : ∀ j v, v ∉ B →
      |u j v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    (hsum : ∀ j, Summable fun v => |u j v - 1|) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ j, κ ≤ ∏' v, u j v := by
  classical
  let V := {v : HeightOneSpectrum (𝓞 F) // v ∉ B}
  let d : V → ℝ := fun v => 2 / (Ideal.absNorm v.1.asIdeal : ℝ) ^ 2
  have hd : Summable d := by
    have h := ((Primes.summable_one_div_absNorm_sq F).mul_left 2).comp_injective
      (i := fun v : V => v.1) Subtype.val_injective
    exact h.congr fun v => by simp [d, Function.comp_apply, div_eq_mul_inv]
  have hd0 (v : V) : 0 ≤ d v := by dsimp [d]; positivity
  have hd1 (v : V) : d v < 1 := by
    have hq : (2 : ℝ) ≤ Ideal.absNorm v.1.asIdeal := by exact_mod_cast Growth.two_le_norm v.1
    dsimp [d]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hs : Summable fun v : V => |(1 - d v) - 1| := hd.congr fun v => by
    rw [show 1 - d v - 1 = -(d v) by ring, abs_neg, abs_of_nonneg (hd0 v)]
  have low := AbsTprod.abs_tprod V (fun v => 1 - d v) hs
  let K := ∏' v : V, (1 - d v)
  have hK : 0 < K := low.2.2.1 fun v => sub_pos.mpr (hd1 v)
  refine ⟨(∏ v ∈ B, u 0 v) * K, mul_pos (Finset.prod_pos hpos) hK, ?_⟩
  intro j
  obtain ⟨hm, hspl⟩ := (AbsTprod.abs_tprod _ _ (hsum j)).2.1 B
  rw [hspl, Finset.prod_congr rfl (fun v hv => hbad j v hv)]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_pos hpos).le
  apply le_of_tendsto_of_tendsto' low.1.hasProd hm.hasProd
  intro T
  apply Finset.prod_le_prod (fun v _ => (sub_pos.mpr (hd1 v)).le)
  intro v _
  have h := (abs_le.mp (hgood j v.1 v.2)).1
  change 1 - 2 / (Ideal.absNorm v.1.asIdeal : ℝ)^2 ≤ u j v.1
  linarith

/-- The norms used in Q belong to their own ideals. Adding a multiple of Q
to one therefore gives a unit at every exceptional place. -/
theorem avoids {R : Type} [CommRing R] (I : Ideal R) (proper : I ≠ ⊤)
    (Q j : ℕ) (hQ : (Q : R) ∈ I) : ((1 + Q*j : ℕ) : R) ∉ I := by
  intro h
  have h' := I.sub_mem h (I.mul_mem_right (j : R) hQ)
  have h1 : (1 : R) ∈ I := by simpa using h'
  exact proper ((Ideal.eq_top_iff_one _).mpr h1)

theorem geometric_exceeds (N p k : ℕ) (hN : 0 < N) (hp : 2 ≤ p) :
    k < N * p ^ k := ((Nat.lt_two_pow_self (n := k)).trans_le (Nat.pow_le_pow_left hp k)).trans_le
      (Nat.le_mul_of_pos_left _ hN)

theorem progression_step (N Q j : ℕ) :
    N*(1+Q*(j+1)) = N*(1+Q*j) + N*Q := by ring

end DensityReplay
#print axioms DensityReplay.uniform_product
#print axioms DensityReplay.avoids
#print axioms DensityReplay.geometric_exceeds
#print axioms DensityReplay.progression_step
