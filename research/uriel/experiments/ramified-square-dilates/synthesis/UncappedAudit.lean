import UncappedGrowth
import OptimalSupport
import GaussianSharp
import Lean.Util.FoldConsts
open Lean Meta Elab Command

namespace UncappedAudit

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
  let refs ← projectClosure `UncappedGrowth.all_multiples
  checkMembership refs #[`OriginalFloor.punctured_floor, `CoordinateFloor.lower, `HaarSlices.average,
    `GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le, `ExceptionalPrimeCriterion.uncapped_iff,
    `GermSupport.nonzero_at] #[`GlobalTheory.CompanionTheory.SW.Growth.growth_main,
      `ProgressionGrowth.progression_growth, `DyadicWave.fiber_mass]
  let opt ← projectClosure `OptimalSupport.positive_iff_multiple
  checkMembership opt #[`OriginalFloor.punctured_floor, `OptimalSupport.local_threshold] #[`GlobalTheory.CompanionTheory.SW.Growth.growth_main]
  let concrete ← projectClosure `DyadicWave.sharp_floor
  checkMembership concrete #[`DyadicWave.fiber_mass, `DyadicWave.with_unit] #[`UncappedGrowth.all_multiples]
  logInfo m!"All-multiples closure: {refs.size} project and study constants. Optimal support: {opt.size}. Dyadic sharp-floor closure: {concrete.size}. Membership checks passed."
end UncappedAudit
