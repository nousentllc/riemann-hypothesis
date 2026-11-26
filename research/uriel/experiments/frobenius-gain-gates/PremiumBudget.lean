import NativeGates
import NativeVisits

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory GlobalTheory.EX
open scoped BigOperators

namespace FrobeniusGain
noncomputable section

/-- For an interior prime, a small uniform window on the numerator
and on the retained capacity yields a first-visit residual of at least b'/2. -/
theorem first_visit_residual (s : Scale) {p u c : ℝ}
    (hp : 0 < p) (hpy : p ≤ s.X'/2)
    (hu : (7/8)*s.a ≤ u) (hc : c ≤ (5/4)*s.b') :
    s.b'/2 ≤ max 0 (u/p-c) := by
  have hy : 0 < s.X' := Real.exp_pos _
  have ha : 0 < s.a := mul_pos (by linarith [s.one_lt_alt]) (Real.exp_pos _)
  have hb : 0 < s.b' := div_pos ha hy
  have hyb : s.b' * s.X' = s.a := div_mul_cancel₀ _ hy.ne'
  have hbmul := mul_le_mul_of_nonneg_left hpy hb.le
  have hdiv : (7/4)*s.b' ≤ u/p := by
    apply (le_div_iff₀ hp).2
    nlinarith only [hu,hyb,hbmul]
  exact le_trans (by linarith : s.b'/2 ≤ u/p-c) (le_max_right _ _)

/-- A local credit exceeding the total price and raw loss beats both
fallback thresholds, independently of the sign of the fallback. -/
theorem premium_lower {gU g0 price loss credit margin : ℝ}
    (hl : 0 ≤ loss) (h0 : -loss ≤ g0) (hC : credit ≤ gU-g0)
    (h : price+loss+margin ≤ credit) :
    margin ≤ gU-price-max g0 0 := by
  have hg : max g0 0 ≤ g0+loss := max_le (by linarith) (by linarith)
  linarith

/-- A summed obstruction yields one actual row with positive slack.
The weights themselves need only be nonnegative. -/
theorem positive_row {ι : Type*} (T : Finset ι) (w c b : ι → ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i)
    (h : ∑ i ∈ T, w i * b i < ∑ i ∈ T, w i * c i) :
    ∃ i ∈ T, b i < c i := by
  by_contra! hn
  exact h.not_ge (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hn i hi) (hw i hi))

/-- The selected inert orbit stays live through the outer cutoff in gainP. -/
theorem outer_guard_false {B : Arith.Base} {p : ℕ} {h : B.R.A}
    (hneq : h ≠ 0) (hp : (p : ℝ) < B.sc.X') :
    ¬ ((B.IsResidueClassZero p ∧ h = 0) ∨ B.sc.X'' B.R.n < (p : ℝ)) := by
  have hy : 0 < B.sc.X' := Real.exp_pos _
  have hx : 1 ≤ B.sc.x := B.sc.one_lt_alt.le
  have hn : 1 ≤ (B.R.n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt B.R.ord_pos
  have ha : 0 < B.sc.a := mul_pos (by linarith) (Real.exp_pos _)
  have he : B.sc.X'' B.R.n = B.sc.X' * (B.sc.x * B.R.n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  have hy' : B.sc.X' ≤ B.sc.X'' B.R.n := by
    rw [he]
    simpa using mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hx hn) hy.le
  exact not_or.mpr ⟨fun h0 => hneq h0.2, not_lt_of_ge (hp.le.trans hy')⟩

/-- Membership in the actual VV and one strict local premium increase the
whole gainP relative to its g0-only value with the same inputs. -/
theorem strict_gain_over_fallback {B : Arith.Base} {I : Arith.Ins B} {K : G.Consts}
    {a b : B.R.A → ℤ} {h t : B.R.A} {p j : ℕ} {oj : Bool × B.R.A → ℝ}
    (hneq : h ≠ 0) (hp : (p : ℝ) < B.sc.X')
    (ht : t ∈ Arith.Loc.VV B I K a b h p)
    (hgain : max (Arith.Loc.g0 B I K a b h p j oj t) 0 <
      Arith.Loc.gU B I K a b h p j oj t - Arith.Loc.Pr B I K b h p j oj t) :
    (∑ r ∈ Arith.Loc.reps B I h p, max (Arith.Loc.g0 B I K a b h p j oj r) 0) <
      Arith.Loc.gainP B I K a b h p j oj := by
  classical
  let V := Arith.Loc.VV B I K a b h p
  let J := Arith.Loc.reps B I h p
  let f := fun r => max (Arith.Loc.g0 B I K a b h p j oj r) 0
  let g := fun r => max (Arith.Loc.gU B I K a b h p j oj r -
    Arith.Loc.Pr B I K b h p j oj r) (f r)
  have hsub : V ⊆ J := by
    unfold V Arith.Loc.VV
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hlt : ∑ r ∈ V, f r < ∑ r ∈ V, g r :=
    Finset.sum_lt_sum (fun r _ => le_max_right _ _) ⟨t,ht,lt_max_of_lt_left hgain⟩
  have union := Finset.sum_sdiff hsub (f := f)
  rw [Arith.Loc.gainP,if_neg (outer_guard_false hneq hp)]
  change ∑ r ∈ J, f r < (∑ r ∈ V, g r) + ∑ r ∈ J \ V, f r
  linarith only [hlt,union]

end
end FrobeniusGain

#print axioms FrobeniusGain.first_visit_residual
#print axioms FrobeniusGain.premium_lower
#print axioms FrobeniusGain.positive_row
#print axioms FrobeniusGain.outer_guard_false
#print axioms FrobeniusGain.strict_gain_over_fallback
