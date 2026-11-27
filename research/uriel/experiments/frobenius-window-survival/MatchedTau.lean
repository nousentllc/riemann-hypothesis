import Predecessor
import NativeAccounting

open Formalism.BasicNotions Formalism.HC Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory
open scoped BigOperators

namespace FrobeniusWindow
noncomputable section

private theorem inert_partner {B : Arith.Base} {p : ℕ} (hc : B.IsResidueClassZero p)
    (h t : B.R.A) (e : ℕ) : Arith.Loc.partner B h p t e = (false,t+e • h) := by
  have hn : ¬ B.IsSg p := by
    change ¬ B.cls p = .signal
    change B.cls p = .inertClass at hc
    rw [hc]
    decide
  simp [Arith.Loc.partner,hn]

private theorem point_forward {B : Arith.Base} {h t : B.R.A}
    (s : Fin (addOrderOf h)) (e : ℕ) :
    t + (G.posAdd s e : ℕ) • h = (t + (s : ℕ) • h) + e • h := by
  change t + ((s.val+e)%addOrderOf h) • h = _
  rw [mod_addOrderOf_nsmul,add_nsmul,add_assoc]

def slotMinimum (B : Arith.Base) (a b : B.R.A → ℤ) (h t : B.R.A)
    (p j : ℕ) (off : Bool × B.R.A → ℝ) (x : Fin (addOrderOf h)) (e : ℕ) : ℝ :=
  max 0 (min (Arith.Loc.al B a (t+(x : ℕ) • h)/(p : ℝ)^e)
    (Arith.Loc.capU B b h p j off (t+(x : ℕ) • h) e))

set_option maxHeartbeats 800000 in
open Classical in
/-- The native tau head is covered by a finite subset of even-anchor minima,
up to the subtraction from a in the supply numerator. -/
theorem tau_head_paid {B : Arith.Base} {a b : B.R.A → ℤ} {h t : B.R.A} {p j : ℕ}
    {off : Bool × B.R.A → ℝ} (hc : B.IsResidueClassZero p) (he : Even (addOrderOf h))
    (hp : 1 ≤ (p : ℝ)) (hcg : 0 ≤ B.cG)
    (hoff : ∀ s ∈ B.TT, B.kaJ j ≤ off (false,s)+B.cG) :
    let T := Arith.Loc.topsPos B h t
    tauHead B a b h t p ≤
      (∑ u ∈ T.filter G.IsTypeV ×ˢ (Finset.range (addOrderOf h)).filter Odd,
        slotMinimum B a b h t p j off u.1 u.2) + (T.card : ℝ)*(2*B.cG) := by
  classical
  intro T
  let cost := fun y : Fin (addOrderOf h) =>
    min (Arith.Loc.wPos B h t b y : ℝ)
      ((Arith.Loc.wPos B h t a (source T y) : ℝ)/(p : ℝ)^G.dMinus T y)
  let M := slotMinimum B a b h t p j off
  have cover (y : Fin (addOrderOf h)) (hy : y ∈ T) (_ : ¬ G.IsTypeV y)
      (h0 : G.dMinus T y ≠ 0) : cost y-2*B.cG ≤ M (source T y) (G.dMinus T y) := by
    have hy' : t+(y : ℕ) • h ∈ B.TT := (Finset.mem_filter.mp hy).2
    have hloc : (t+(source T y : ℕ) • h) + G.dMinus T y • h = t+(y : ℕ) • h := by
      rw [← point_forward,source_returns T y h0]
    have hcap : (b (t+(y : ℕ) • h) : ℝ) ≤
        Arith.Loc.capU B b h p j off (t+(source T y : ℕ) • h) (G.dMinus T y) := by
      unfold Arith.Loc.capU Arith.Loc.fillG
      rw [inert_partner hc,hloc]
      simp only [Arith.Loc.fill,hy',true_and,if_true]
      linarith only [hoff _ hy']
    have hq : 1 ≤ (p : ℝ)^G.dMinus T y := one_le_pow₀ hp
    have hs : (2*B.cG)/((p : ℝ)^G.dMinus T y) ≤ 2*B.cG :=
      div_le_self (by positivity) hq
    have hcost := charged_min_le (a := (Arith.Loc.wPos B h t a (source T y) : ℝ))
      (q := (p : ℝ)^G.dMinus T y) (show 0 < (p : ℝ)^G.dMinus T y by linarith)
      (show 0 ≤ 2*B.cG by positivity) hcap
    change cost y ≤ _ at hcost
    have hM : min (Arith.Loc.al B a (t+(source T y : ℕ) • h)/(p : ℝ)^G.dMinus T y)
        (Arith.Loc.capU B b h p j off (t+(source T y : ℕ) • h) (G.dMinus T y)) ≤
        M (source T y) (G.dMinus T y) := le_max_right _ _
    unfold Arith.Loc.wPos at hcost
    unfold Arith.Loc.al at hM
    linarith only [hcost,hs,hM]
  have hm := charge_matching he T (fun y => cost y-2*B.cG) M
    (fun x e => le_max_left _ _) cover
  have hsum : tauHead B a b h t p ≤ (∑ y ∈ T.filter (fun y => ¬ G.IsTypeV y),
      if G.dMinus T y = 0 then 0 else cost y-2*B.cG) +
      ((T.filter (fun y => ¬ G.IsTypeV y)).card : ℝ)*(2*B.cG) := by
    change (∑ y ∈ T.filter (fun y => ¬ G.IsTypeV y),
      if G.dMinus T y = 0 then 0 else cost y) ≤ _
    rw [← nsmul_eq_mul,← Finset.sum_const,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    by_cases h0 : G.dMinus T y = 0 <;> simp [h0,hcg]
  have htC : ((T.filter (fun y => ¬ G.IsTypeV y)).card : ℝ) ≤ T.card := by
    exact_mod_cast Finset.card_filter_le _ _
  linarith only [hm,hsum,mul_le_mul_of_nonneg_right htC (show 0 ≤ 2*B.cG by positivity)]

/-- Finite selection of the same prime after all three costs are booked. -/
theorem pay_joint_budget {P : Type*} (S : Finset P)
    (w credit cost : P → ℝ) (hn : ∀ p ∈ S, 0 ≤ w p)
    (h : ∑ p ∈ S, w p*cost p < ∑ p ∈ S, w p*credit p) :
    ∃ p ∈ S, cost p < credit p := by
  by_contra! hc
  exact h.not_ge (Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hc p hp) (hn p hp))

theorem premium_after_costs {premium tau io extra weight credit budget : ℝ}
    (h1 : 2*credit ≤ premium-tau+extra)
    (h2 : extra+weight*io ≤ budget) (h3 : budget < credit) :
    credit < premium-tau-weight*io := by
  linarith only [h1,h2,h3]

end
end FrobeniusWindow

#print axioms FrobeniusWindow.tau_head_paid
#print axioms FrobeniusWindow.pay_joint_budget
#print axioms FrobeniusWindow.premium_after_costs
