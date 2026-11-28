import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

noncomputable section

namespace UrielJoint

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.HC GlobalTheory.EX UpperTheory.Top UpperTheory.Comparison₂

/-- A property expressible on the plain host axes available to any family requirement. -/
def withRow (ψ : PChar) : FReq := fun s φ H TT t =>
  GChi ψ s φ H TT t ∧ ∃ Y : ℝ, PairWin s Y ∧ Rowq Y s.eps (H.QS / 4) H.q H.d

/-- Keep the original host, ranks and chosen scale set. HostGood supplies its row. -/
theorem supply_withRow {ψ : PChar} {la : ℝ} (supply : HostExW la (GChi ψ).req) :
    HostExW la (withRow ψ).req := by
  intro eps hpos hsmall
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hS⟩ := supply eps hpos hsmall
  refine ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, ?_⟩
  intro s hs hx hmem
  obtain ⟨R, H, q0, hrank, hCT, hgood, hχ⟩ := hS s hs hx hmem
  obtain ⟨Y, hwin, hrow⟩ := hgood.1.1
  exact ⟨R, H, q0, hrank, hCT, hgood, hχ, Y, hwin, (pairRow_iff_rowq Y s.eps H).1 hrow⟩

/-- All three predicates use the host at i, with Y a prime-pair scale. -/
def JointAt {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ (i : Fm.Ix x) (Y : ℝ),
    PairWin (Fm.L x i).sc Y ∧ PairRow Y eps (Fm.D x i).host ∧
    VVle (Fm.D x i).host.E (Fm.D x i).R.t (Real.sqrt (Fm.L x i).sc.b) ∧
    CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x

/-- The published design has QDRowsF internally. Keep it when extracting the family. -/
theorem jointAt_of_qdRowsF {ψ : PChar} {la eps : ℝ} {Fm : FamP eps}
    (rows : QDRowsF Fm) (hχ : (GChi ψ).cls la Fm)
    {eD eL K cHH eK CL x₀ : ℝ}
    (ties : ∀ x ≥ x₀, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x) :
    ∃ X : ℝ, ∀ x ≥ X, x ∈ Fm.Win → JointAt Fm eD eL K cHH eK x := by
  obtain ⟨xr, hr⟩ := rows
  refine ⟨max xr (max x₀ (Fm.x1 + 1)), ?_⟩
  intro x hx hwin
  have hlate : Fm.x1 < x := by
    have := (le_max_right x₀ (Fm.x1 + 1)).trans ((le_max_right xr _).trans hx)
    linarith
  have hchain := ties x ((le_max_left x₀ _).trans ((le_max_right xr _).trans hx)) hwin
  obtain ⟨i, hcore⟩ := tiedCore_of_chainTied Fm _ _ _ _ _ _ _ hchain
  obtain ⟨Y, hbounds, hrow⟩ := hr x ((le_max_left xr _).trans hx) i
  refine ⟨i, Y, ?_, hrow, (hχ.2 x hlate i).2, hcore⟩
  change (Fm.L x i).sc.x ^ (1 / (Fm.L x i).sc.J) ≤ Y ∧ Y ≤ (Fm.L x i).sc.x
  simpa only [Fm.L_x x i hlate, Fm.L_J x i] using hbounds

/-- TopG with the enriched requirement produces late joint witnesses for a single family.
    Its character supply is precisely the original one, and its arbitrarily late
    power windows are retained. -/
theorem family_with_joint_witness (ψ : PChar) {la : ℝ} (hla : 1 < la) (top : TopG)
    (supply : HostExW la (GChi ψ).req) :
    ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
      ∃ Fm : FamP eps, Fm.toFamCore.Windows la ∧
        ∃ K cHH eK X : ℝ, ∀ x ≥ X, x ∈ Fm.Win → JointAt Fm eD eL K cHH eK x := by
  have hV : ∀ {eps : ℝ} (Fm : FamP eps), (withRow ψ).cls la Fm → HypV Fm.toFamCore := by
    intro eps Fm h
    exact hypV_of_cls ψ la Fm ⟨h.1, fun x hx i => (h.2 x hx i).1⟩
  obtain ⟨eD, eL, ε₁, hε₁, hF⟩ := top la (withRow ψ) hla (supply_withRow supply) hV
  refine ⟨eD, eL, ε₁, hε₁, ?_⟩
  intro eps hpos hsmall
  obtain ⟨Fm, hc, K, cHH, eK, CL, x₀, ties⟩ := hF eps hpos hsmall
  refine ⟨Fm, hc.1, K, cHH, eK, max x₀ (Fm.x1 + 1), ?_⟩
  intro x hx hwin
  have hlate : Fm.x1 < x := by
    have := (le_max_right x₀ (Fm.x1 + 1)).trans hx
    linarith
  have hchain := ties x ((le_max_left x₀ _).trans hx) hwin
  obtain ⟨i, hcore⟩ := tiedCore_of_chainTied Fm _ _ _ _ _ _ _ hchain
  have hi := hc.2 x hlate i
  obtain ⟨Y, hpairwin, hrow⟩ := hi.2
  have hw := (pairRow_iff_rowq Y _ (Fm.D x i).host).2 hrow
  rw [Fm.L_eps x i] at hw
  exact ⟨i, Y, hpairwin, hw, hi.1.2, hcore⟩

end UrielJoint
