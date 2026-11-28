import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC UpperTheory.Top GlobalTheory.EX

namespace FixedLevelWindows

/-- Extract the scalar conclusion prior to applying the localized Landau criterion. -/
theorem ofTied (Λ : Level) (la : ℝ)
    (h : ChebyshevInequalityAtWindowScale (Fam := FamP)
      (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) la Λ) :
    ∀ δ : ℝ, 0 < δ → HasWindows {x | Λ.Gm x ≤ x ^ ((1:ℝ)/2+δ)} la := by
  obtain ⟨eD,eL,ε₁,h1,hfam⟩ := h
  intro δ hδ
  obtain ⟨eps,heps,hsmall,hδeps⟩ := exists_small_eps (eD+eL+7) hδ h1
  obtain ⟨Fm,hE,hW,hT⟩ := hfam eps heps hsmall
  obtain ⟨x1,hx1⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales Λ eD eL eps heps Fm hE hT
  apply ((windows_iff _ la).1 hW).mono (x0 := max x1 1)
  intro x hx hw
  exact (hx1 x (le_of_max_le_left hx) hw).trans
    (Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hx) (by linarith))

/-- A single fixed character suffices: the width of its host is preserved. -/
theorem ofCharacter (ψ : PChar) (la : ℝ) (hla : 1 < la) (hG : TopG)
    (hs : HostExW la (GChi ψ).req) :
    ∀ δ : ℝ, 0 < δ → HasWindows {x | (Level.cyc ψ).Gm x ≤ x ^ ((1:ℝ)/2+δ)} la := by
  apply ofTied
  obtain ⟨eD,eL,ε₁,h1,hsupply⟩ := hG la (GChi ψ) hla hs (hypV_of_cls ψ la)
  refine ⟨eD,eL,ε₁,h1,?_⟩
  intro eps heps hsmall
  obtain ⟨Fm,hcls,htied⟩ := hsupply eps heps hsmall
  exact ⟨Fm,eFamC_of_cls ψ la Fm hcls,hcls.1,htied⟩

/-- One cofinal common window contains both boundary ordinates. -/
theorem twoEndpoints (ψ : PChar) (la : ℝ) (hla : 1 < la) (hG : TopG)
    (hs : HostExW la (GChi ψ).req) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ Y : ℝ, B ≤ Y ∧ 1 ≤ Y ∧
      (Level.cyc ψ).Gm Y ≤ Y ^ ((1:ℝ)/2+δ) ∧
      (Level.cyc ψ).Gm (Y^la) ≤ (Y^la) ^ ((1:ℝ)/2+δ) := by
  obtain ⟨Y,hY,hw⟩ := ofCharacter ψ la hla hG hs δ hδ (max B 1)
  have hY1 : 1 ≤ Y := (le_max_right _ _).trans hY
  have hy := Real.self_le_rpow_of_one_le hY1 hla.le
  exact ⟨Y,(le_max_left _ _).trans hY,hY1,hw Y le_rfl hy,hw _ hy le_rfl⟩

end FixedLevelWindows
#print axioms FixedLevelWindows.ofTied
#print axioms FixedLevelWindows.ofCharacter
#print axioms FixedLevelWindows.twoEndpoints
