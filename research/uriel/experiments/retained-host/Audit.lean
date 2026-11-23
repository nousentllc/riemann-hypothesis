import Development.AutomorphicArithmetic.ShortNorms.hostOfFieldOf
import Development.AutomorphicArithmetic.ShortNorms.supplyOfAdmOf
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Each pair must be present in the compiled proof body as a direct constant reference.
run_cmd do
  let b := "UpperTheory.BernoulliSumsFrobeniusOrbits."
  let t := "UpperTheory.Top."
  let c := "UpperTheory.Comparison₂."
  let s := "UpperTheory.T3."
  let edges := [
    (b ++ "topsGroup", b ++ "select"),
    (b ++ "topsGroup", b ++ "shares_of_counts"),
    (b ++ "topsGroup", b ++ "orbit_sum"),
    (b ++ "topsGroup", b ++ "not_good_le"),
    (b ++ "topsFrame", b ++ "topsGroup"),
    (b ++ "topsBase", b ++ "topsFrame"),
    (b ++ "topsChoiceH", b ++ "topsBase"),
    (s ++ "hostOfFieldOf", b ++ "topsChoiceH"),
    (s ++ "hostOfFieldOf", t ++ "pairRows"),
    (s ++ "supplyOfAdmOf", t ++ "boundedTw"),
    (s ++ "supplyOfAdmOf", t ++ "winPairs"),
    (s ++ "supplyOfAdmOf", "QH.pairEx"),
    ("QH.pairEx", "QH.pair_exists"),
    ("QH.pairEx", "QH.kappa4"),
    (c ++ "charsA", c ++ "tops_sum"),
    (c ++ "core_gm", c ++ "charsA"),
    (c ++ "core_gm", c ++ "gmA_eq"),
    (c ++ "core_gm", c ++ "sigA_le"),
    (t ++ "zeroFreeAll_of_topG", t ++ "eFamC_of_cls")]
  for (caller, callee) in edges do
    let info ← getConstInfo caller.toName
    let some v := info.value? (allowOpaque := true) | throwError "No proof body for {caller}"
    unless v.getUsedConstants.contains callee.toName do
      throwError "Missing direct reference {caller} to {callee}"
    let axioms := ((← collectAxioms caller.toName).map Name.toString).qsort (· < ·)
    let row := Json.mkObj [("caller", toJson caller), ("callee", toJson callee), ("axioms", toJson axioms)]
    IO.println ("RETAINED_EDGE " ++ row.compress)
