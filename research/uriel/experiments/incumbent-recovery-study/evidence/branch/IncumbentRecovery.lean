import ActualGain

noncomputable section
open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit
open Classical
variable {D : D7} {L : SizeData₂ D}

def fallbackRecovery (X : Inst D L) (K : Consts) (a b : HH D → ℤ)
    (p j : ℕ) (t : HH D) : ℝ :=
  max 0 (max (g0 X K a b p j t) 0 - (gU X K a b p j t - Pr X K b p j t))

/-- An absent successor has the capped thin-place height even if its orbit is otherwise occupied. -/
theorem hole_cap (X : Inst D L) (b : HH D → ℤ) {p j : ℕ} (hc : IsResidueClassZero D p)
    (hj : j ∈ SizeData₂.lifts D) (s : HH D) (hole : s+hP D p ∉ D.host.TT) :
    capU X b p j s 1 ≤ L.sc.w'' D.R.n + L.etaSz + cG L := by
  have hthin : IsThinPl D (false, s+hP D p) := by
    simp [IsThinPl, IsTopPl, IsThickPl, hole]
  have hb := (X.off_thin j _ hthin).2
  have hk := kaJ_nonneg D j hj
  unfold capU fillG fill
  rw [partner_of_central hc, one_nsmul]
  simp only [and_false, hole, if_false, zero_add]
  linarith

/-- Uniform price bound on a fixed orbit whose first successors are all absent.
    The hypotheses are imposed on the existing data; no subset is selected. -/
theorem no_successor_credit (X : Inst D L) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p j : ℕ} (hp : p.Prime)
    (hc : IsResidueClassZero D p) (hn : hP D p ≠ 0) (hp3 : 2*L.sc.X' ≤ (p : ℝ)^3)
    (hj : j ∈ SizeData₂.lifts D) (t : HH D)
    (holes : ∀ s ∈ topsOn X p t, s+hP D p ∉ D.host.TT) :
    credit X a b p j t ≤ ∑ s ∈ (topsOn X p t).filter (IsV X p),
      (capU X b p j s 1 + al L a s / ((p : ℝ)*((p : ℝ)^2-1))) := by
  have hc1 : (∑ s ∈ topsOn X p t, first X a b p j s) =
      ∑ s ∈ (topsOn X p t).filter (IsV X p), minCredit X a b p j s 1 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    rw [first_directed X a b hc hn]
    simp only [if_neg (holes s hs)]
  have hsum := (bulk_credit_interval X P hW hp hp3 hj t).2
  rw [hc1] at hsum
  rw [Finset.sum_add_distrib]
  exact hsum.trans (add_le_add (Finset.sum_le_sum fun s _ =>
    min_le_right (al L a s / (p : ℝ)^1) (capU X b p j s 1)) le_rfl)

/-- Every hole row contributes its entire adjusted supply above the first cap.
    This can certify that the zero floor never decides the fallback. -/
theorem no_successor_direct_lower (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p j : ℕ} (hp : p.Prime)
    (hc : IsResidueClassZero D p) (hn : hP D p ≠ 0) (hj : j ∈ SizeData₂.lifts D)
    (t : HH D) (holes : ∀ s ∈ topsOn X p t, s+hP D p ∉ D.host.TT) :
    (∑ s ∈ topsOn X p t, (al L a s / (p : ℝ) - capU X b p j s 1)) -
       dl X K p t ≤ g0 X K a b p j t := by
  have hsum := (orbit_tail_budget X P hW hp hj t).1
  unfold g0
  apply sub_le_sub_right
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro s hs
  have hh := (excl_one_iff hc hn s).not.mpr (holes s hs)
  simp [firstBase, hh, posDemand]

/-- Any price beyond the upper credit certificate is recovered by the fallback. -/
theorem recovery_lower (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p j : ℕ} (hp : p.Prime)
    (hj : j ∈ SizeData₂.lifts D) (t : HH D) {upper : ℝ}
    (h : credit X a b p j t ≤ upper) :
    Pr X K b p j t - upper ≤ fallbackRecovery X K a b p j t := by
  have hh := raw_difference X K P hW hp hj t
  unfold fallbackRecovery
  have h1 := le_max_left (g0 X K a b p j t) 0
  have h2 := le_max_right 0 (max (g0 X K a b p j t) 0 -
      (gU X K a b p j t - Pr X K b p j t))
  linarith

/-- When the direct gain is nonnegative and price covers credit, full recovery is exact. -/
theorem recovery_eq_price_sub_credit (X : Inst D L) (K : Consts) (P : ParameterChoice' D L)
    {a b : HH D → ℤ} (hW : InWin L a b) {p j : ℕ} (hp : p.Prime)
    (hj : j ∈ SizeData₂.lifts D) (t : HH D)
    (hd : 0 ≤ g0 X K a b p j t) (hc : credit X a b p j t ≤ Pr X K b p j t) :
    fallbackRecovery X K a b p j t = Pr X K b p j t - credit X a b p j t := by
  have h := raw_difference X K P hW hp hj t
  unfold fallbackRecovery
  rw [max_eq_left hd, max_eq_right (by linarith)]
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit

open Formalism.MainNotions.AuxBlock8.Pf.St.GainAudit
#print axioms no_successor_credit
#print axioms hole_cap
#print axioms no_successor_direct_lower
#print axioms recovery_lower
#print axioms recovery_eq_price_sub_credit
