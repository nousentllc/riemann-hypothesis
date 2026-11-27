import RamPlaceEndpoint
import RamFieldRamification
import RamBasePrimitive
import Lean.Util.FoldConsts
open Lean Meta Elab Command

namespace RamDependencyAudit

/-- All top-level roots of source modules in the pinned project, followed by this
study's proof modules. Dependencies below Core and Mathlib cannot refer back to
modules built after those libraries. Use module provenance rather than the name
of a declaration, since the pinned proof also adds declarations to other namespaces. -/
private def roots : Array Name :=
  #[`OptimalSupport,`ShellThreshold,`SingularJump,`BuildAid, `CompanionTheory, `Development, `Formalism, `GroundTheory, `Lemmata, `Main, `PositivityTheory, `ReciprocityTheory, `Statements, `Supplements, `AllDepth, `BlockIdentification, `Contact, `CoordinateFloor, `Cylinders, `DenominatorControl, `DyadicBase, `DyadicLocal, `Endpoint, `EvenDescent, `ExceptionalDilation, `ExceptionalPrimeCriterion, `Existence, `FiniteCounts, `FloorTransfer, `FourBase, `FourContact, `FourCounts, `FourEndpoint, `FourEven, `FourLift, `FourNeighborhood, `FourTubes, `GaussianDilates, `GaussianField, `GaussianSharp, `GaussianTrace, `GermSupport, `GrowthSandwich, `HaarSlices, `LocalChart, `LocalIsotropy, `LocalPair, `LocalRegularSupport, `LocalTube, `LocalWitnesses, `Nearby, `NeighborhoodGrowth, `Neighborhoods, `OddSquares, `OptimalSupport, `OriginalFloor, `PrimeBlocks, `PrimitiveLift, `ProgressionGrowth, `Shallow, `ShellThreshold, `SingularGaussian, `SingularJump, `SingularZero, `SquareDepth, `Tubes, `UncappedGrowth]

/-- Follow references in elaborated kernel types and values, including opaque proof
terms, with the inductive/constructor/recursor handling of getUsedConstantsAsSet. -/
private def projectClosure (root : Name) : CoreM (Std.HashSet Name) := do
  let env ← getEnv
  let allowed := env.allImportedModuleNames.map fun mod => roots.any (·.isPrefixOf mod) || mod.toString.startsWith "Ram"
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
  let all ← projectClosure `RamPlaceEndpoint.original
  let real ← projectClosure `RamPlaceEndpoint.realized
  let main := #[`RamBase.count_four, `RamBase.census_six, `RamBase.pivot_permutation,
    `RamLift.orbit_count, `RamBridge.normalized, `RamGlobal.gram_matrix, `RamGlobal.isCM,
    `RamFieldPlace.valuation_equiv, `RamPlaceCompletion.integer_preimage,
    `RamField.cyl_mass, `RamField.small_four, `RamTransport.fiber_count_to_tube,
    `RamTransportPlace.mass_on_latV, `GlobalTheory.CompanionTheory.SW.FibreRatio.ratio_field]
  checkMembership all main #[`TargetFour.total_mass,`RamBase.Five.primitive_card]
  checkMembership real #[`RamPlaceEndpoint.original,`RamTransportForm.family_exists] #[]
  logInfo m!"Named-place audit: {all.size} project and study declarations for the universal endpoint, {real.size} for existence. Explicit dependency and control checks passed."
end RamDependencyAudit
