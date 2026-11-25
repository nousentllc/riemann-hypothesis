import CompanionTheory.AutomorphicTheory.ThetaDilations.SwOne
import OriginalGrowthControl
import ProgressionEndpoint
import Lean.Util.FoldConsts

/-! Read-only audit of elaborated endpoint types and their proof-term dependencies.
The original endpoint is imported for comparison; neither new endpoint imports it. -/
open Lean Meta Elab Command

namespace EndpointAudit

/-- All top-level roots of source modules in the pinned project, followed by this
study's proof modules. Dependencies below Core and Mathlib cannot refer back to
modules built after those libraries. Use module provenance rather than the name
of a declaration, since the pinned proof also adds declarations to other namespaces. -/
private def roots : Array Name :=
  #[`BuildAid, `CompanionTheory, `Development, `Formalism, `GroundTheory, `Lemmata,
    `Main, `PositivityTheory, `ReciprocityTheory, `Statements, `Supplements,
    `ProgressionGeometry, `ProgressionGrowth, `ProgressionEndpoint, `GrowthConsumer,
    `OriginalGrowthConsumer, `RankOneConsumer, `OriginalGrowthControl]

/-- Follow references in elaborated kernel types and values, including opaque proof
terms, with the inductive/constructor/recursor handling of getUsedConstantsAsSet. -/
private def projectClosure (root : Name) : CoreM (Std.HashSet Name) := do
  let env ← getEnv
  let allowed := env.allImportedModuleNames.map fun mod => roots.any (·.isPrefixOf mod)
  let kernel := env.checked.get
  let mut seen : Std.HashSet Name := {}
  let mut pending := #[root]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := kernel.find? name | throwError "Absent kernel constant {name}"
      for dep in info.getUsedConstantsAsSet do
        let some idx := env.getModuleIdxFor? dep | throwError "Unknown owner of {dep}"
        if allowed[idx.toNat]! && !seen.contains dep then
          pending := pending.push dep
  return seen

private def checkMembership (refs : Std.HashSet Name) (yes no : Array Name) : CoreM Unit := do
  for name in yes do
    unless refs.contains name do throwError "Expected reachable declaration {name}"
  for name in no do
    if refs.contains name then throwError "Unexpected reachable declaration {name}"

run_cmd liftTermElabM do
  let original := `CompanionTheory.PlacePermOperatorBicommutantSpan.sw_one
  let pinned := `GrowthConsumer.sw_one_via_pinned_growth
  let alternative := `ProgressionEndpoint.sw_one_via_progression
  let originalType := (← getConstInfo original).type
  for name in #[pinned, alternative] do
    let otherType := (← getConstInfo name).type
    unless ← isDefEq otherType originalType do throwError "Endpoint type differs for {name}"
    logInfo m!"AUDIT Elaborated type matches pinned sw_one: {name}"
  let growth := `GlobalTheory.CompanionTheory.SW.Growth.growth_main
  let progression := `ProgressionGrowth.progression_growth
  let shared := #[`GrowthConsumer.sw_one_of_growth, `GrowthConsumer.original_scalar_comparison,
                  `GrowthConsumer.forces_iff_relativeGrowth]
  let alternateRefs ← projectClosure alternative
  checkMembership alternateRefs (shared ++ #[`ProgressionEndpoint.provider, progression])
    #[original, growth, `GlobalTheory.T.exists_frequently_mul_pow_le_tprod_rank_one_local_density]
  let controlRefs ← projectClosure pinned
  checkMembership controlRefs (shared ++ #[growth]) #[original, progression]
  logInfo m!"AUDIT Progression proof traversal passed: {alternateRefs.size} project/study constants"
  logInfo m!"AUDIT Pinned growth control traversal passed: {controlRefs.size} project/study constants"

end EndpointAudit
