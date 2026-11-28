import MarkedSupply
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi
import Development.AutomorphicArithmetic.ShortNorms.hostOfFieldOf

open UpperTheory.Top Formalism.BasicNotions Formalism.MainNotions Formalism.HC
open GlobalTheory.EX HostParam.Seam

theorem MarkedWindows.hostFromInputs
    (hNorm : UpperTheory.T3.ShortNorm) (hOne : UpperTheory.T3.SmallOne) (ψ : PChar)
    (lam : ℝ) (hlam : lam < 2 ∨ lam = 2 ∧ ψ = PChar.one) (hV : VWinAt ψ 401) :
    MarkedWindows.MarkedHost ψ lam (GChi ψ).req := by
  refine MarkedWindows.supplyWithSupport lam (UpperTheory.T3.hostOfFieldOf hNorm hOne) ψ hlam hV ?_
  intro eps he0 he1
  obtain ⟨x0,hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi

#print axioms MarkedWindows.hostFromInputs
