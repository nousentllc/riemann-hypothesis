import HostInputs
import LevelWindows

open Formalism.HC UpperTheory.Top GlobalTheory.EX
namespace MarkedWindows

theorem scalarBelowTwo (top : TopG) (hn : UpperTheory.T3.ShortNorm) (hs : UpperTheory.T3.SmallOne)
    (ψ : PChar) (hv : VWinAt ψ 401) {lam : ℝ} (lo : 1 < lam) (hi : lam < 2) :
    ∀ δ : ℝ, 0 < δ → HasWindows {x | (Level.cyc ψ).Gm x ≤ x ^ ((1:ℝ)/2+δ)} lam :=
  FixedLevelWindows.ofCharacter ψ lam lo top (hostFromInputs hn hs ψ lam (Or.inl hi) hv).forget

theorem principalScalar (top : TopG) (hn : UpperTheory.T3.ShortNorm) (hs : UpperTheory.T3.SmallOne)
    (hv : VWinAt PChar.one 401) :
    ∀ δ : ℝ, 0 < δ → HasWindows {x | Deduction.G x ≤ x ^ ((1:ℝ)/2+δ)} 2 := by
  have h := FixedLevelWindows.ofCharacter PChar.one 2 (by norm_num) top
    (hostFromInputs hn hs PChar.one 2 (Or.inr ⟨rfl,rfl⟩) hv).forget
  simpa only [principalLevel] using h

end MarkedWindows
#print axioms MarkedWindows.scalarBelowTwo
#print axioms MarkedWindows.principalScalar
