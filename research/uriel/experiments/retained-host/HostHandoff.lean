import JointControls

noncomputable section

namespace UrielRetained

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.HC GlobalTheory.EX UpperTheory.Top UpperTheory.Comparison₂ UrielJoint

/-- Two fields used by different parts of the calculation, evaluated at the same host. -/
def ObservableInputs (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A)
    (x eps : ℝ) : Prop :=
  φ.Shares TT (x ^ (-1 + eps)) ∧
    ∀ θ ∈ H.Bounded Λ.KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      H.IsPrimOf θ χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log x

/-- The local row scale Y can differ from the beginning of a family window. -/
def ChosenAt (ψ : PChar) {eps : ℝ} (F : FamP eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ (i : F.Ix x) (Y : ℝ),
    PairWin (F.L x i).sc Y ∧ PairRow Y eps (F.D x i).host ∧
    VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b) ∧
    EAtH (Level.cyc ψ) (F.D x i).host.toHostRaw (F.D x i).host.TT x eps 4 ∧
    ObservableInputs (Level.cyc ψ) (F.D x i).host.toHostRaw (F.D x i).host.TT x eps ∧
    CoreAtH (F.D x i).host.toHostRaw (F.D x i).host.TT eD eL K cHH eK eps x ∧
    (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

/-- Extend a previously joined witness, taking its EAtH only after its index is fixed. -/
theorem extend_joint {ψ : PChar} {la eps : ℝ} {F : FamP eps}
    (hχ : (GChi ψ).cls la F) (heps : 0 < eps) {eD eL K cHH eK X₀ : ℝ}
    (joint : ∀ x ≥ X₀, x ∈ F.Win → JointAt F eD eL K cHH eK x) :
    ∃ X : ℝ, ∀ x ≥ X, x ∈ F.Win → ChosenAt ψ F eD eL K cHH eK x := by
  obtain ⟨Xg, hg⟩ := core_gm (Level.cyc ψ) eD eL K cHH eK 4 eps heps
  refine ⟨max Xg (max X₀ (F.x1 + 1)), ?_⟩
  intro x hx hxWin
  have hlower := (le_max_right Xg _).trans hx
  have hlate : F.x1 < x := by
    have := (le_max_right X₀ (F.x1 + 1)).trans hlower
    linarith
  obtain ⟨i, Y, hwin, hrow, hv, hcore⟩ := joint x ((le_max_left X₀ _).trans hlower) hxWin
  have hE := (hχ.2 x hlate i).1
  rw [F.L_x x i hlate, F.L_eps x i] at hE
  exact ⟨i, Y, hwin, hrow, hv, hE, ⟨hE.shares, hE.bdL⟩, hcore,
    hg x ((le_max_left Xg _).trans hx) _ (F.D x i).host.toHostAx (F.D x i).host.TT hE hcore⟩

/-- Thresholds and family are fixed before taking an arbitrarily late whole interval. -/
def FamilyHandoff (ψ : PChar) (la : ℝ) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
    ∃ F : FamP eps, F.toFamCore.Windows la ∧ ∃ K cHH eK X : ℝ,
      (∀ x ≥ X, x ∈ F.Win → ChosenAt ψ F eD eL K cHH eK x) ∧
      ∀ y : ℝ, ∃ W : ℝ, max y (max 1 X) ≤ W ∧
        ∀ x : ℝ, W ≤ x → x ≤ W ^ la → x ∈ F.Win ∧ ChosenAt ψ F eD eL K cHH eK x

theorem of_design {ψ : PChar} {la : ℝ}
    (design : FamilyClassConnected (fun F => QDRowsF F ∧ (GChi ψ).cls la F)) :
    FamilyHandoff ψ la := by
  obtain ⟨eD, eL, ε₁, hε, select⟩ := design
  refine ⟨eD, eL, ε₁, hε, ?_⟩
  intro eps hp hs
  obtain ⟨F, ⟨rows, hχ⟩, K, cHH, eK, CL, x₀, ties⟩ := select eps hp hs
  obtain ⟨X₀, hj⟩ := jointAt_of_qdRowsF rows hχ ties
  obtain ⟨X, hall⟩ := extend_joint hχ hp hj
  refine ⟨F, hχ.1, K, cHH, eK, X, hall, ?_⟩
  intro y
  obtain ⟨W, hW, interval⟩ := hχ.1 (max y (max 1 X))
  refine ⟨W, hW, ?_⟩
  intro x hWx hx
  have hmem := interval x hWx hx
  exact ⟨hmem, hall x ((le_max_right 1 X).trans ((le_max_right y _).trans (hW.trans hWx))) hmem⟩

open UrielJoint.DesignDefinitions

/-- Specialization to the same hypotheses as the final design call in the pinned TopShape. -/
theorem of_original_character_design (𝒜 : FamClass) (ψ : PChar) (la : ℝ)
    (hEx : DesignExists (WithTw (WithSm (WithChN (fun Fm => 𝒜 Fm ∧ (GChi ψ).cls la Fm)))) 3)
    (hN : Closed (D3 3 𝒜) fun Fm _ => LinkN Fm)
    (hEta : Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm 2 CH)
    (hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm)
    (hS : Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3)
    (hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0) :
    FamilyHandoff ψ la :=
  of_design (originalDesign_with_qdRows 𝒜 (GChi ψ) la hEx (hypV_of_cls ψ la)
    hN hEta hIRR hZ hDIV hRk hG hS hGL)

/-- This universal characterization quantifies over arbitrary (possibly singleton) core selectors. -/
theorem extend_every_selector_iff {ι : Type*} (E : ι → Prop) :
    (∀ P : ι → Prop, (∃ i, P i) → ∃ i, P i ∧ E i) ↔ ∀ i, E i := by
  constructor
  · intro h j
    obtain ⟨i, hij, hE⟩ := h (fun i => i = j) ⟨j, rfl⟩
    exact hij ▸ hE
  · intro h P hP
    obtain ⟨i, hi⟩ := hP
    exact ⟨i, hi, h i⟩

theorem independently_existing_disjoint :
    (∃ i : Bool, i = false) ∧ (∃ i : Bool, i = true) ∧
      ¬ ∃ i : Bool, i = false ∧ i = true := by decide

/-- A raw EAtH at j cannot fill the goal at i. Transport along j = i repairs it. -/
theorem index_transport_control {eps x : ℝ} (ψ : PChar) (F : FamP eps)
    (i j : F.Ix x) (same : j = i)
    (h : EAtH (Level.cyc ψ) (F.D x j).host.toHostRaw (F.D x j).host.TT x eps 4) :
    EAtH (Level.cyc ψ) (F.D x i).host.toHostRaw (F.D x i).host.TT x eps 4 := by
  fail_if_success exact h
  cases same
  exact h

/-- Even with equal cardinalities, directly substituting a share proof at U fails.
    Transport along equality of the sets supplies the positive control. -/
theorem shares_transport_control {φ : Frame} (U T : Finset φ.A) (δ : ℝ)
    (_same_card : U.card = T.card) (same_set : U = T) (h : φ.Shares U δ) :
    φ.Shares T δ := by
  fail_if_success exact h
  cases same_set
  exact h

end UrielRetained

#print axioms UrielRetained.of_original_character_design
#print axioms UrielRetained.extend_every_selector_iff
#print axioms UrielRetained.independently_existing_disjoint
