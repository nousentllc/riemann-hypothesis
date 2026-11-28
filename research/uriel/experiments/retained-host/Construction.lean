import StrongHost
import StrongSupply
import StrongWindow
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

noncomputable section

namespace UrielRetained

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC
open GlobalTheory.EX UpperTheory.Top HostParam.Seam

/-- The strengthened set comes with the host and the original character requirement. -/
theorem strong_host_supply (ψ : PChar) (hV : VWinAt ψ 401)
    (hN : UpperTheory.T3.ShortNorm) (hP : UpperTheory.T3.SmallOne) :
    HostExW (3 / 2) (strongReq ψ).req := by
  refine UpperTheory.T3.supplyOfAdmOf_inv (UpperTheory.T3.hostOfFieldOf_inv hN hP) ψ hV ?_
  intro eps he hs
  obtain ⟨x0, late⟩ := admissibleClassesTwistedChar eps he hs
  refine ⟨x0, fun s φ H hsx hx hlo hhi _ _ => ?_⟩
  subst hsx
  exact late s φ H rfl hx hlo hhi

/-- This conclusion retains the stronger share estimate on the index used for the prime bound. -/
theorem strong_window_from_inputs (ψ : PChar) (top : TopG) (hV : VWinAt ψ 401)
    (hN : UpperTheory.T3.ShortNorm) (hP : UpperTheory.T3.SmallOne) :
    StrongFamilyHandoff ψ (3 / 2) :=
  strong_window_of_top ψ (by norm_num) top (strong_host_supply ψ hV hN hP)

#print axioms strong_host_supply
#print axioms strong_window_from_inputs

end UrielRetained
