import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory
open scoped BigOperators

namespace FrobeniusWindow
noncomputable section

def rowPremium (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p j : ℕ) (oj : Bool × B.R.A → ℝ)
    (t : B.R.A) : ℝ :=
  max 0 (Arith.Loc.gU B I K a b h p j oj t - Arith.Loc.Pr B I K b h p j oj t -
    max (Arith.Loc.g0 B I K a b h p j oj t) 0)

def orbitPremium (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) (off : ℕ → Bool × B.R.A → ℝ)
    (t : B.R.A) : ℝ :=
  ∑ j ∈ B.lifts, rowPremium B I K a b h p j (off j) t

open Classical in
def primePremium (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) (off : ℕ → Bool × B.R.A → ℝ) : ℝ :=
  ∑ t ∈ Arith.Loc.VV B I K a b h p, orbitPremium B I K a b h p off t

def fallback (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p j : ℕ) (oj : Bool × B.R.A → ℝ) : ℝ :=
  ∑ t ∈ Arith.Loc.reps B I h p, max (Arith.Loc.g0 B I K a b h p j oj t) 0

theorem vv_subset (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) :
    Arith.Loc.VV B I K a b h p ⊆ Arith.Loc.reps B I h p := by
  classical
  unfold Arith.Loc.VV
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

private theorem max_split (b u : ℝ) : max u b = b + max 0 (u-b) := by
  by_cases h : u ≤ b
  · rw [max_eq_right h,max_eq_left (sub_nonpos.mpr h),add_zero]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h)),max_eq_right (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]
    ring

open Classical in
theorem gain_split {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h : B.R.A} {p j : ℕ} {oj : Bool × B.R.A → ℝ}
    (hguard : ¬ ((B.IsResidueClassZero p ∧ h=0) ∨ B.sc.X'' B.R.n < (p : ℝ))) :
    Arith.Loc.gainP B I K a b h p j oj =
      fallback B I K a b h p j oj +
      ∑ t ∈ Arith.Loc.VV B I K a b h p, rowPremium B I K a b h p j oj t := by
  rw [Arith.Loc.gainP,if_neg hguard]
  let V := Arith.Loc.VV B I K a b h p
  let J := Arith.Loc.reps B I h p
  let f := fun t => max (Arith.Loc.g0 B I K a b h p j oj t) 0
  let u := fun t => Arith.Loc.gU B I K a b h p j oj t - Arith.Loc.Pr B I K b h p j oj t
  change (∑ t ∈ V, max (u t) (f t)) + (∑ t ∈ J \ V, f t) =
    (∑ t ∈ J, f t) + (∑ t ∈ V, max 0 (u t-f t))
  simp_rw [max_split (f _) (u _)]
  rw [Finset.sum_add_distrib]
  have hs := Finset.sum_sdiff (vv_subset B I K a b h p) (f := f)
  change (∑ t ∈ J \ V, f t) + (∑ t ∈ V, f t) = ∑ t ∈ J, f t at hs
  linarith only [hs]

theorem gain_lift_split {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h : B.R.A} {p : ℕ} {off : ℕ → Bool × B.R.A → ℝ}
    (hguard : ¬ ((B.IsResidueClassZero p ∧ h=0) ∨ B.sc.X'' B.R.n < (p : ℝ))) :
    (∑ j ∈ B.lifts, Arith.Loc.gainP B I K a b h p j (off j)) =
      (∑ j ∈ B.lifts, fallback B I K a b h p j (off j)) +
      primePremium B I K a b h p off := by
  classical
  simp_rw [gain_split hguard]
  rw [Finset.sum_add_distrib,primePremium]
  congr 1
  unfold orbitPremium
  exact Finset.sum_comm

theorem orbitPremium_nonneg (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) (off : ℕ → Bool × B.R.A → ℝ) (t : B.R.A) :
    0 ≤ orbitPremium B I K a b h p off t :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

theorem primePremium_nonneg (B : Arith.Base) (I : Arith.Ins B) (K : G.Consts)
    (a b : B.R.A → ℤ) (h : B.R.A) (p : ℕ) (off : ℕ → Bool × B.R.A → ℝ) :
    0 ≤ primePremium B I K a b h p off :=
  Finset.sum_nonneg fun t _ => orbitPremium_nonneg B I K a b h p off t

/-- Keep the source's prime-wide maximum and integer ceiling in the accounting. -/
theorem io_le_premium {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h : B.R.A} {p : ℕ} {off : ℕ → Bool × B.R.A → ℝ}
    (hσ : 0 ≤ Arith.Loc.Sig B I K a b h p) :
    Arith.Loc.ioP B I K a b h p off ≤
      2 * Arith.Loc.Sig B I K a b h p * (primePremium B I K a b h p off + 1) := by
  classical
  unfold Arith.Loc.ioP
  split_ifs with hv
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases Finset.exists_mem_eq_sup' hv (fun t => Arith.Loc.Sv B I K a b h p off t) with ⟨t,ht,heq⟩
    rw [heq]
    change ((⌈orbitPremium B I K a b h p off t⌉ : ℤ) : ℝ) ≤ _
    have hceil := (Int.ceil_lt_add_one (orbitPremium B I K a b h p off t)).le
    have hrow : orbitPremium B I K a b h p off t ≤ primePremium B I K a b h p off :=
      Finset.single_le_sum (fun r _ => orbitPremium_nonneg B I K a b h p off r) ht
    linarith
  · exact mul_nonneg (by positivity)
      (by linarith [primePremium_nonneg B I K a b h p off])

def tauHead (B : Arith.Base) (a b : B.R.A → ℤ) (h t : B.R.A) (p : ℕ) : ℝ :=
  open Classical in
  let T := Arith.Loc.topsPos B h t
  let n := addOrderOf h
  ∑ y ∈ T.filter (fun y => ¬ G.IsTypeV y),
    if G.dMinus T y = 0 then 0 else
      min (Arith.Loc.wPos B h t b y : ℝ)
        ((Arith.Loc.wPos B h t a (G.posAdd y (n-G.dMinus T y)) : ℝ)/(p : ℝ)^G.dMinus T y)

def tauRemainder (B : Arith.Base) (K : G.Consts) (h t : B.R.A) (p : ℕ) : ℝ :=
  let n := addOrderOf h
  let N := (Arith.Loc.topsPos B h t).card
  K.kappaThresholdOne * (N : ℝ) * (G.N1 B.sc : ℝ) *
    (B.sc.a / (p : ℝ)^2 + G.La K B.sc * B.sc.a / ((p : ℝ)*B.R.k)) +
  K.kappaThresholdTwo * (N : ℝ) * (G.Qp B.sc p * Arith.Loc.c6f B K p n +
    (B.R.k : ℝ) * G.Qp B.sc p + (B.R.k : ℝ) * Real.logb p B.sc.a + B.cG) +
  2 * (n : ℝ) * B.cG

theorem tau_large_eq {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h : B.R.A} {p : ℕ}
    (hv : (Arith.Loc.VV B I K a b h p).Nonempty) (hp : B.sc.p0 B.R.k ≤ (p : ℝ)) :
    Arith.Loc.tauP B I K a b h p =
      (I.ep p : ℝ) + ∑ t ∈ Arith.Loc.VV B I K a b h p,
      (B.R.m : ℝ) *
        ((⌈tauHead B a b h t p + tauRemainder B K h t p⌉₊ : ℝ) + (Arith.Loc.Dp B K h p : ℝ) + 1) := by
  classical
  rw [Arith.Loc.tauP,if_neg hv.ne_empty]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Arith.Loc.tv,if_neg (not_lt.mpr hp)]
  have ht : Arith.Loc.tIf B K p (addOrderOf h) (Arith.Loc.topsPos B h t)
      (Arith.Loc.wPos B h t a) (Arith.Loc.wPos B h t b) = tauHead B a b h t p + tauRemainder B K h t p := by
    unfold Arith.Loc.tIf tauHead tauRemainder
    ring
  rw [ht]

end
end FrobeniusWindow

#print axioms FrobeniusWindow.gain_lift_split
#print axioms FrobeniusWindow.io_le_premium
#print axioms FrobeniusWindow.tau_large_eq
