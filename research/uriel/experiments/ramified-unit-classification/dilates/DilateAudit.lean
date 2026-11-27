import DilateEndpoint
import DilateSixteen
import DilateBoundary
import FourEndpoint
import RamBasePrimitive
import Lean.Util.FoldConsts
open Lean Meta Elab Command

namespace DilateAudit

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
  let allowed := env.allImportedModuleNames.map fun mod => roots.any (·.isPrefixOf mod) || mod.toString.startsWith "Ram" || mod.toString.startsWith "Dilate"
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
  let env ← getEnv
  for name in yes ++ no do
    unless env.contains name do throwError "Audit requested absent declaration {name}"
  for name in yes do
    unless refs.contains name do throwError "Expected reachable declaration {name}"
  for name in no do
    if refs.contains name then throwError "Unexpected reachable declaration {name}"


run_cmd liftTermElabM do
  let universal ← projectClosure `RamDilate.original
  let existence ← projectClosure `RamDilate.realized
  let contact ← projectClosure `RamDilate.contact_sixteen
  let boundary ← projectClosure `RamDilate.last_shortfall
  let finite := #[`RamDilate.counts, `RamDilate.at_square, `RamDilate.from_strata,
    `RamDilate.primitive_multiple, `RamDilate.Contact.primitive_zero,
    `RamDilate.Pivot.primitive_shift, `RamBase.five_digit_pivot,
    `RamDilate.imprim_double_nat, `RamDilate.Descent.double_count,
    `RamDilate.low3_four, `RamDilate.low4_eight, `RamBase.census_six]
  let measure := #[`DilateTransport.original, `DilateTransport.small,
    `DilateTransport.unit_count, `DilateTransport.tube,
    `RamGlobal.gram_matrix, `RamPlaceCompletion.integer_preimage,
    `RamTransportForm.original_mass, `GlobalTheory.CompanionTheory.SW.FibreRatio.ratio_field]
  let controls := #[`RamDilate.contact_sixteen, `TargetFour.total_mass,
    `RamBase.Five.primitive_card, `RamDilate.last_shortfall, `RamDilate.Boundary.strict]
  checkMembership universal (finite ++ measure) controls
  checkMembership existence (finite ++ #[`DilateTransport.realized, `RamTransportForm.family_exists]) #[]
  checkMembership contact #[`RamBase.census_six] #[`RamDilate.from_strata,
    `RamDilate.primitive_multiple, `RamDilate.imprim_double_nat, `RamTransportForm.original_mass]
  checkMembership boundary #[`RamDilate.Boundary.strict, `RamDilate.zero_residue,
    `RamDilate.Boundary.zero_counts, `RamDilate.imprim_double_nat, `RamDilate.primitive_multiple]
    #[`RamDilate.from_strata, `DilateTransport.original, `RamTransportForm.original_mass]
  logInfo m!"Square-dilate audit: {universal.size} project and study declarations for the universal endpoint, {existence.size} for existence, {contact.size} for the target-16 contact count, {boundary.size} for the sharp cutoff witness. Finite-chain, transport, existence and exclusion checks passed."
end DilateAudit
