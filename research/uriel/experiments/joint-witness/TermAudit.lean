import JointControls
import SameIndex
import Development.AutomorphicArithmetic.ShortNorms.supplyOfAdmOf
import Development.AutomorphicArithmetic.ShortNorms.hostOfFieldOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let names := ["UpperTheory.V.Win.thmBab_of", "UpperTheory.V.jointWin_of", "UpperTheory.V.vwinAt_of_joint",
    "UpperTheory.T3.hostOfFieldOf", "UpperTheory.T3.supplyOfAdmOf", "UpperTheory.Top.vvRecord",
    "UpperTheory.Top.divinN_of_hypV", "UpperTheory.Top.topDesWin", "UpperTheory.Comparison₂.tiedCore_of_chainTied",
    "UrielJoint.sameIndex", "UrielJoint.sameIndexInput", "UrielJoint.supply_withRow",
    "UpperTheory.Top.originalDesign_with_qdRows", "UrielJoint.jointAt_of_qdRowsF",
    "UrielJoint.family_with_joint_witness", "UrielJoint.joint_of_design",
    "UrielJoint.joint_of_original_character_design"]
  for s in names do
    let n := s.toName
    let info ← getConstInfo n
    let some v := info.value? (allowOpaque := true) | throwError "missing proof body at {n}"
    let ax ← collectAxioms n
    let sorted := fun (a : Array Name) => (a.map Name.toString).qsort (· < ·)
    let obj := Json.mkObj [("name", toJson s), ("type",toJson (sorted info.type.getUsedConstants)),
      ("proof",toJson (sorted v.getUsedConstants)), ("axioms",toJson (sorted ax))]
    IO.println ("JOINT_TERM " ++ obj.compress)
