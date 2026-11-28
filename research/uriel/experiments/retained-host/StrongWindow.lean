import HostHandoff

noncomputable section

namespace UrielRetained

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.HC GlobalTheory.EX UpperTheory.Top UpperTheory.Comparison₂ UrielJoint

def strongReq (ψ : PChar) : FReq := fun s φ H TT t =>
  φ.Shares TT s.x⁻¹ ∧ GChi ψ s φ H TT t

private def strongWithRow (ψ : PChar) : FReq := fun s φ H TT t =>
  φ.Shares TT s.x⁻¹ ∧ withRow ψ s φ H TT t

private theorem supply_rows {ψ : PChar} {la : ℝ} (supply : HostExW la (strongReq ψ).req) :
    HostExW la (strongWithRow ψ).req := by
  intro eps hpos hsmall
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hS⟩ := supply eps hpos hsmall
  refine ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, ?_⟩
  intro s hs hx hmem
  obtain ⟨R, H, q0, hrank, hCT, hgood, hinv, hχ⟩ := hS s hs hx hmem
  obtain ⟨Y, hwin, hrow⟩ := hgood.1.1
  exact ⟨R, H, q0, hrank, hCT, hgood, hinv, hχ, Y, hwin, (pairRow_iff_rowq Y s.eps H).1 hrow⟩

/-- Centered character sums for characters trivial on the subgroup but nontrivial on the full A-factor. -/
def InverseCharacterBound (φ : Frame) (TT : Finset φ.A) (x : ℝ) : Prop :=
  ∀ χ ∈ Deduction.CH.PsiA φ.A0, (¬ ∀ t : φ.A, χ (0, t) = 1) →
    ‖(∑ t ∈ TT, χ (0, t)) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤
      φ.o * x⁻¹ * (TT.card : ℝ)

def StrongChosenAt (ψ : PChar) {eps : ℝ} (F : FamP eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ (i : F.Ix x) (Y : ℝ), (F.D x i).R.toFrame.Shares (F.D x i).host.TT x⁻¹ ∧
    InverseCharacterBound (F.D x i).R.toFrame (F.D x i).host.TT x ∧
    PairWin (F.L x i).sc Y ∧ PairRow Y eps (F.D x i).host ∧
    VVle (F.D x i).host.E (F.D x i).R.t (Real.sqrt (F.L x i).sc.b) ∧
    EAtH (Level.cyc ψ) (F.D x i).host.toHostRaw (F.D x i).host.TT x eps 4 ∧
    ObservableInputs (Level.cyc ψ) (F.D x i).host.toHostRaw (F.D x i).host.TT x eps ∧
    CoreAtH (F.D x i).host.toHostRaw (F.D x i).host.TT eD eL K cHH eK eps x ∧
    (Level.cyc ψ).Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def StrongFamilyHandoff (ψ : PChar) (la : ℝ) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
    ∃ F : FamP eps, F.toFamCore.Windows la ∧ ∃ K cHH eK X : ℝ,
      (∀ x ≥ X, x ∈ F.Win → StrongChosenAt ψ F eD eL K cHH eK x) ∧
      ∀ y : ℝ, ∃ W : ℝ, max y (max 1 X) ≤ W ∧
        ∀ x : ℝ, W ≤ x → x ≤ W ^ la → x ∈ F.Win ∧ StrongChosenAt ψ F eD eL K cHH eK x

/-- Run the family construction with the strengthened host requirement before choosing any index.
    Both the row predicate and the stronger share refer to the host built by this single supply. -/
theorem strong_window_of_top (ψ : PChar) {la : ℝ} (hla : 1 < la) (top : TopG)
    (supply : HostExW la (strongReq ψ).req) : StrongFamilyHandoff ψ la := by
  have character : ∀ {eps : ℝ} {F : FamP eps}, (strongWithRow ψ).cls la F → (GChi ψ).cls la F :=
    fun h => ⟨h.1, fun x hx i => (h.2 x hx i).2.1⟩
  obtain ⟨eD, eL, ε₁, hε, select⟩ := top la (strongWithRow ψ) hla (supply_rows supply)
    (fun F h => hypV_of_cls ψ la F (character h))
  refine ⟨eD, eL, ε₁, hε, ?_⟩
  intro eps hp hs
  obtain ⟨F, hc, K, cHH, eK, CL, x₀, ties⟩ := select eps hp hs
  have rows : QDRowsF F := by
    refine ⟨F.x1 + 1, ?_⟩
    intro x hx i
    have hl : F.x1 < x := by linarith
    obtain ⟨Y, win, rowq⟩ := (hc.2 x hl i).2.2
    have row := (pairRow_iff_rowq Y _ (F.D x i).host).2 rowq
    unfold PairWin at win
    refine ⟨Y, ?_, ?_⟩
    · simpa only [F.L_x x i hl, F.L_J x i] using win
    · rw [F.L_eps x i] at row
      exact row
  obtain ⟨X₀, hj⟩ := jointAt_of_qdRowsF rows (character hc) ties
  obtain ⟨X₁, chosen⟩ := extend_joint (character hc) hp hj
  let X := max X₁ (F.x1 + 1)
  have hall : ∀ x ≥ X, x ∈ F.Win → StrongChosenAt ψ F eD eL K cHH eK x := by
    intro x hx hwin
    obtain ⟨i, Y, rest⟩ := chosen x ((le_max_left X₁ _).trans hx) hwin
    have hl : F.x1 < x := by
      have := (le_max_right X₁ (F.x1 + 1)).trans hx
      linarith
    have hinv := (hc.2 x hl i).1
    rw [F.L_x x i hl] at hinv
    exact ⟨i, Y, hinv, tops_sum _ _ x⁻¹ hinv, rest⟩
  refine ⟨F, hc.1, K, cHH, eK, X, hall, ?_⟩
  intro y
  obtain ⟨W, hW, interval⟩ := hc.1 (max y (max 1 X))
  refine ⟨W, hW, ?_⟩
  intro x hWx hx
  have hmem := interval x hWx hx
  exact ⟨hmem, hall x ((le_max_right 1 X).trans ((le_max_right y _).trans (hW.trans hWx))) hmem⟩

end UrielRetained

#print axioms UrielRetained.strong_window_of_top
