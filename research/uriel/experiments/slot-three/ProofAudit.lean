import SlotApplication
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let names := ["SlotThree.CyclotomicTransport.class_card", "SlotThree.CyclotomicTransport.all_layers_iff",
    "SlotThree.standard_common_lift", "SlotThree.FieldModel.fieldModel", "SlotThree.source_cZero", "SlotThree.quotient_bound",
    "SlotThree.tower_module_zero", "SlotThree.layer_zero", "SlotThree.any_center", "SlotThree.actualABound",
    "SlotThree.firstBound_of_card", "SlotThree.weight_iff", "SlotThree.zero_weights",
    "SlotThree.singleton_weights", "SlotThree.certified_opposite", "SlotThree.certified_one",
    "SlotThree.same_lift_opposite", "SlotThree.common_lift", "SlotThree.partB_for_center"]
  for name in names do
    let n := name.toName
    let decl ← getConstInfo n
    let some proof := decl.value? (allowOpaque := true) | throwError "Missing body for {n}"
    let sorted := fun (a : Array Name) => (a.map Name.toString).qsort (· < ·)
    let row := Json.mkObj [("name", toJson name), ("axioms", toJson (sorted (← collectAxioms n))),
      ("type", toJson (sorted decl.type.getUsedConstants)), ("body", toJson (sorted proof.getUsedConstants))]
    IO.println ("SLOT3_AUDIT " ++ row.compress)
