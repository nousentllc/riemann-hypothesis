import Lean.CoreM
import Lean.Replay

open Lean

/-- Replay project constants into an environment containing only Mathlib and its
imports. The name list is generated from the checked original-source import graph. -/
unsafe def main (args : List String) : IO Unit := do
  let [listPath] := args | throw <| IO.userError "Supply one file with module names"
  initSearchPath (← findSysroot)
  let names := ((← IO.FS.readFile listPath).splitOn "\n").filter (· != "")
  withImportModules #[{module := `Mathlib}] {} fun baseline => do
    let mut added : Std.HashMap Name ConstantInfo := {}
    let mut repeated := 0
    for m in names do
      let file ← findOLean m.toName
      let mut files := #[file]
      for l in [OLeanLevel.server, OLeanLevel.private] do
        let part := l.adjustFileName file
        if ← part.pathExists then files := files.push part
      let data ← readModuleDataParts files
      let some (part, _) := data.back? | throw <| IO.userError s!"no module data for {m}"
      for n in part.constNames, info in part.constants do
        if let some prior := baseline.toKernelEnv.find? n <|> added[n]? then
          unless prior.type == info.type && prior.levelParams == info.levelParams do throw <| IO.userError s!"duplicate type differs: {n}"
          unless prior.isTheorem && info.isTheorem do
            unless prior.value? == info.value? do throw <| IO.userError s!"duplicate body differs: {n}"
          repeated := repeated + 1
        else
          if info.isAxiom then throw <| IO.userError s!"additional project axiom: {n}"
          if info.getUsedConstantsAsSet.contains `sorryAx then throw <| IO.userError s!"placeholder: {n}"
          added := added.insert n info
    IO.println s!"Replaying {added.size} project declarations from {names.length} modules into Mathlib. Shared declaration names: {repeated}."
    (← IO.getStdout).flush
    let checked ← baseline.replay added
    let mut skipped := 0
    for (n, info) in added do
      if info.isUnsafe || info.isPartial then
        skipped := skipped + 1
      else
        unless (checked.toKernelEnv.find? n).isSome do throw <| IO.userError s!"missing after replay: {n}"
    IO.println s!"Kernel accepted and located {added.size-skipped} project declarations. Unsafe or partial records skipped by replay: {skipped}."
