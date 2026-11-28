import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import UrielFragments
import UrielControls
import UrielSharpness
import Lean
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

private def sortedNames (xs : Array Name) : Array String :=
  (xs.map Name.toString).qsort (· < ·)

private def analyticName (n : Name) : Bool :=
  n.toString.startsWith "Deduction." ||
    n.toString.startsWith "_private.Development.AutomorphicArithmetic.DedekindLFunctions."

run_cmd do
  let ns := ["Deduction.zeroFree_of_rpow_window", "Deduction.lemmaL", "Deduction.windowHyp_of_rpow",
    "Deduction.poleData", "Deduction.landau_window", "Deduction.landau_window_key",
    "Deduction.landau_window_contra", "Deduction.landau_nearest", "Deduction.landau_nearest_equi",
    "Deduction.landau_pole_asym", "Deduction.landau_cauchy", "Deduction.landau_tails",
    "Deduction.landau_window_ineq", "Deduction.landau_growth_contra", "UpperTheory.V.Win.window1",
    "GlobalTheory.CutNum.numeric", "GlobalTheory.EX.exists_even_between", "UrielExperiment.slopeCoefficient_iff",
    "UrielControl.usesInjected"]
  for s in ns do
    let n := s.toName
    let info ← getConstInfo n
    let some v := info.value? (allowOpaque := true) | throwError "Missing proof for {n}"
    let ax ← collectAxioms n
    let mod ← findModuleOf? n
    let j := Json.mkObj [("name", toJson s), ("module", toJson (mod.map Name.toString)),
      ("type", toJson (sortedNames info.type.getUsedConstants)),
      ("value", toJson (sortedNames v.getUsedConstants)), ("axioms", toJson (sortedNames ax))]
    IO.println ("URIEL_TERM " ++ j.compress)
  let mut pending := (ns.map String.toName).toArray.filter analyticName
  let mut visited : Std.HashSet Name := {}
  while let some n := pending.back? do
    pending := pending.pop
    unless visited.contains n do
      visited := visited.insert n
      let info ← getConstInfo n
      let children := ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      let localRefs := children.filter analyticName
      let j := Json.mkObj [("name", toJson n.toString), ("value", toJson (sortedNames localRefs))]
      IO.println ("URIEL_EDGE " ++ j.compress)
      pending := pending ++ localRefs

#print axioms Deduction.zeroFree_of_rpow_window
#print axioms UpperTheory.V.Win.window1
#print axioms GlobalTheory.CutNum.numeric
#print axioms GlobalTheory.EX.exists_even_between
#print axioms UrielExperiment.slopeCoefficient_iff
#print axioms UrielControl.usesInjected
