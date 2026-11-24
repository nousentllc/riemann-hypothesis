import OriginalSlices

open Filter
open scoped Topology Classical

namespace UrielCheck.SiegelWeil
open PositivityTheory.SiegelWeilFormula.Gen.WL

/-- At a nonzero index position the affine argument has special value M-i.
    The last index exists only for positive n. -/
theorem min_euler_exponent (M n : ℕ) (hn : 0 < n) :
    ∀ i : Fin n, (M : ℤ) - (n - 1 : ℕ) ≤ (M : ℤ) - (i : ℕ) ∧
      ((M : ℤ) - (n - 1 : ℕ) = (M : ℤ) - (i : ℕ) ↔ (i : ℕ) = n - 1) := by
  intro i
  have := i.isLt
  constructor <;> omega

theorem scalar_at_special_point (M n i : ℕ) :
    2 * (((M : ℂ) - n) / 2) + n - i = (M : ℂ) - i := by ring

/-- The denominator order budget leaves exactly one forced order of vanishing. -/
theorem order_budget (c d M n : ℕ) (hd : 1 ≤ d) (h : M < n) :
    let K := ∑ i : Fin n, (if 1 ≤ (M : ℤ) - ((i : ℕ) : ℤ) then 0
      else if (M : ℤ) - ((i : ℕ) : ℤ) = 0 then c+d-1 else d)
    d*(n-M) + c = K+1 ∧ d*(n-M)+c-1 = K := by
  dsimp
  have h' := count c d M n hd h
  omega

/-- If the numerator and denominator orders tie, the punctured identity is
    compatible with a nonzero value. Filling that point with zero need not
    give an analytic function. Here A=G=c=1, K=N, and the point is zero. -/
theorem equal_order_control (K : ℕ) :
    (∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), 1 * (z-0)^K * 1 = (z-0)^K * 1) ∧
    ¬ AnalyticAt ℂ (fun z : ℂ => if z=0 then (0 : ℂ) else 1) 0 := by
  refine ⟨Eventually.of_forall (by simp), ?_⟩
  intro ha
  have ht := ha.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0:ℂ)}ᶜ))
  have he : (fun z : ℂ => if z=0 then (0 : ℂ) else 1) =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 1 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact if_neg hz
  have h0 : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ht.congr' he
  have eq := tendsto_nhds_unique h0 (tendsto_const_nhds (x := (1:ℂ)))
  exact zero_ne_one eq

/-- With the original one-unit order surplus the corrected local model factors
    through a first power. The analytic factor can itself vanish. -/
theorem one_surplus_germ {G A : ℂ → ℂ} {s₀ c : ℂ} (K : ℕ) (hc : c ≠ 0)
    (hA : AnalyticAt ℂ A s₀)
    (hp : ∀ᶠ z in 𝓝[≠] s₀, c * (z-s₀)^K * G z = (z-s₀)^(K+1) * A z) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B s₀ ∧
      (fun z => if z=s₀ then 0 else G z) =ᶠ[𝓝 s₀] fun z => (z-s₀) * B z := by
  refine ⟨fun z => c⁻¹*A z, analyticAt_const.mul hA, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.1 hp] with z hz
  by_cases he : z = s₀
  · simp [he]
  · rw [if_neg he]
    have hw := hz he
    rw [pow_succ] at hw
    apply mul_left_cancel₀ (mul_ne_zero hc (pow_ne_zero K (sub_ne_zero.mpr he)))
    calc
      _ = (z-s₀)^K*(z-s₀)*A z := hw
      _ = _ := by field_simp

end UrielCheck.SiegelWeil
