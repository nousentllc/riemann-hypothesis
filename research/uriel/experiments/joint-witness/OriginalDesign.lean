import Development.AutomorphicArithmetic.CharacterBoxes.DesWin
import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Formalism.SharpRestriction.DesignExistsOfChoices

noncomputable section

namespace UrielJoint.DesignDefinitions

open Formalism.MainNotions

-- The two abbreviations below are verbatim from the pinned CountsIrreducibilityConstants.lean.
abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

end UrielJoint.DesignDefinitions

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions UrielJoint.DesignDefinitions

/-- The final call in TopShape, projecting both the row and the supplied family class
    out of its existing design. All design bounds and inputs are those of that call. -/
theorem originalDesign_with_qdRows (𝒜 : FamClass) (G : FReq) (la : ℝ)
    (hEx : DesignExists (WithTw (WithSm (WithChN (fun Fm => 𝒜 Fm ∧ G.cls la Fm)))) 3)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore)
    (hN : Closed (D3 3 𝒜) fun Fm _ => LinkN Fm)
    (hEta : Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm 2 CH)
    (hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm)
    (hS : Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3)
    (hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0) :
    FamilyClassConnected (fun Fm => QDRowsF Fm ∧ G.cls la Fm) :=
  topDesWin (WithChN 𝒜) (WithChN (fun Fm => 𝒜 Fm ∧ G.cls la Fm))
    (fun Fm => QDRowsF Fm ∧ G.cls la Fm) 2 3 2 0 hEx
    (fun _ hc => ⟨hc.1.1, hc.2⟩)
    (fun _ hc => ⟨hc.2.2.2.2.1, hc.1.2⟩)
    (fun Fm hc => hV Fm hc.2) hN hEta hIRR hZ hDIV hRk hG hS hGL

end UpperTheory.Top
