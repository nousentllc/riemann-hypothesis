import Enriched
import OriginalDesign

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX UpperTheory.Top
open UpperTheory.Comparison₂

namespace UrielJoint

/-- Keep the core and row on the family returned by the strengthened design. -/
theorem joint_of_design {ψ : Formalism.HC.PChar} {la : ℝ}
    (design : FamilyClassConnected (fun F => QDRowsF F ∧ (GChi ψ).cls la F)) :
    ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
      ∃ F : FamP eps, F.toFamCore.Windows la ∧
      ∃ K cHH eK X : ℝ, ∀ x ≥ X, x ∈ F.Win → JointAt F eD eL K cHH eK x := by
  obtain ⟨eD, eL, ε₁, hε, select⟩ := design
  refine ⟨eD, eL, ε₁, hε, ?_⟩
  intro eps hp hs
  obtain ⟨F, ⟨rows, hχ⟩, K, cHH, eK, CL, x₀, ties⟩ := select eps hp hs
  obtain ⟨X, joint⟩ := jointAt_of_qdRowsF rows hχ ties
  exact ⟨F, hχ.1, K, cHH, eK, X, joint⟩

open UrielJoint.DesignDefinitions

/-- At the input of the published design call, retain a family on whose windows
    the prime row, cohomology bound and core are witnessed at one index. -/
theorem joint_of_original_character_design (𝒜 : FamClass) (ψ : Formalism.HC.PChar) (la : ℝ)
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
    ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
      ∃ F : FamP eps, F.toFamCore.Windows la ∧
      ∃ K cHH eK X : ℝ, ∀ x ≥ X, x ∈ F.Win → JointAt F eD eL K cHH eK x :=
  joint_of_design (ψ := ψ) (la := la)
    (originalDesign_with_qdRows 𝒜 (GChi ψ) la hEx (hypV_of_cls ψ la) hN hEta hIRR hZ hDIV hRk hG hS hGL)

end UrielJoint
