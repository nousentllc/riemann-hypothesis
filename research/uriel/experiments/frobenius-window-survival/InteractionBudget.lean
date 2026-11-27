import NativeAccounting
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX
open scoped BigOperators

namespace FrobeniusWindow
noncomputable section

/-- WOK's second summand pays for the surviving interaction charge. -/
theorem wok_sigma_mass {R : Ranks} (s : Scale) (H : Host R) (K : G.Consts)
    (a b : R.A → ℤ) (cD ch : ℝ) (hW : WOK s cD ch K H a b) :
    let B := baseOf s cD ch H
    open Classical in
    (∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => Arith.Loc.Cand B K (hPH H p) p),
      Real.log p / p * Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p) ≤ s.x^(-9 : ℝ)/4 := by
  classical
  intro B
  let P := (Finset.range ⌈s.X'⌉₊).filter (fun p => Arith.Loc.Cand B K (hPH H p) p)
  let v := fun p => Arith.Loc.Sig B (Arith.ins B K 1) K a b (hPH H p) p
  let fail := fun p => s.x^(-s.eps) < v p
  change ∑ p ∈ P, Real.log p / p * v p ≤ _
  change ∑ p ∈ P, Real.log p / p * (2 * (if fail p then (1 : ℝ) else 0) + 4 * v p) ≤ _ at hW
  have point (p : ℕ) (hp : p ∈ P) : 4*(Real.log p / p*v p) ≤
      Real.log p / p*(2*(if fail p then (1 : ℝ) else 0)+4*v p) := by
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hw : 0 ≤ Real.log (p : ℝ)/p :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (by positivity)
    by_cases hf : fail p
    · simp [hf]; linarith
    · simp [hf]; ring_nf; linarith
  have hs := Finset.sum_le_sum point
  rw [← Finset.mul_sum] at hs
  linarith only [hs.trans hW]

/-- A prime-wide ceiling produces a single additive unit, independent of
the number of retained orbits. -/
theorem io_weighted {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} (step : ℕ → B.R.A) (off : ℕ → Bool × B.R.A → ℝ)
    (P : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p)
    (hσ : ∀ p ∈ P, 0 ≤ Arith.Loc.Sig B I K a b (step p) p)
    (hL : ∀ p ∈ P, primePremium B I K a b (step p) p off ≤ L) :
    (∑ p ∈ P, w p * Arith.Loc.ioP B I K a b (step p) p off) ≤
      2*(L+1)*(∑ p ∈ P, w p*Arith.Loc.Sig B I K a b (step p) p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have h1 := io_le_premium (off := off) (hσ p hp)
  have hm : 0 ≤ 2*Arith.Loc.Sig B I K a b (step p) p :=
    mul_nonneg (by norm_num) (hσ p hp)
  have hadd : primePremium B I K a b (step p) p off + 1 ≤ L+1 := by linarith [hL p hp]
  have h2 := mul_le_mul_of_nonneg_left hadd hm
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (hw p hp)
  convert h3 using 1; ring

end
end FrobeniusWindow

#print axioms FrobeniusWindow.wok_sigma_mass
#print axioms FrobeniusWindow.io_weighted
