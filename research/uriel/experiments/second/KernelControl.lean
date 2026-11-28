import Lean

open Lean Elab Command

/- Pass the same explicit proof value to the kernel at two proposed types.
    Both trials start from the same environment, and their returned environments are discarded. -/
run_cmd do
  let base := (← getEnv).toKernelEnv
  let candidate (typeName : String) : Declaration := .thmDecl {
    name := "UrielControl.probe".toName
    levelParams := []
    type := mkConst typeName.toName
    value := mkConst "True.intro".toName
  }
  match base.addDeclCore 0 0 (candidate "True") none with
  | .ok _ => IO.println "positive control accepted: True.intro at True"
  | .error _ => throwError "Kernel rejected the positive control"
  match base.addDeclCore 0 0 (candidate "False") none with
  | .error (.declTypeMismatch _ _ _) => IO.println "negative control rejected: declTypeMismatch at False"
  | .error _ => throwError "Kernel returned an unexpected exception"
  | .ok _ => throwError "Kernel accepted the negative control"
