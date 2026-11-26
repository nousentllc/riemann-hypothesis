# Upstream update review

Reviewed 25 November 2026, America/Detroit. This is a source and change review, not a mathematical referee report or a new proof-verification run.

## Scope and conclusion

The downloaded snapshot is upstream commit `e063a923620ee7787b4a1270421478645bf66bdb`, also preserved in our fork as [baseline/community-2026-11-25](https://github.com/nousentllc/riemann-hypothesis/tree/baseline/community-2026-11-25). This review concerns that fixed snapshot; it does not claim to include later upstream activity.

The useful changes are a much more readable architecture, explicit quantitative interfaces, removal of unused formal machinery, and a more practical build system. The most consequential implication for Nous is that a general architecture guide is no longer an obviously missing contribution. A source-linked explanation of a particular difficult step, or a carefully justified local-density comparison, would be more useful.

I inspected the current guides, build configuration, principal reduction files, relevant measure and density interfaces, the 61 returned history records through the readable-edition import, and selected detailed patches. I also compared the old window interface at the original source pin and our archived study sources. Static inspection covered the source inventory and import graph. I did not read every proof line, reconstruct all historical changes, run Lean, certify equivalence of the old and new developments, or establish novelty against the mathematical literature.

## 1. A replacement architecture, not an ordinary update

Upstream moved to the readable edition from `lsernau/grh-lean` on November 25. The previous community development remains on `alpoge`; our experiments cite the much earlier original source `40e56bab026552e089d7afcfeff08d2defb9c005`. The new and old main branches did not have a common ancestor in the previously checked GitHub comparison. These are separate source lineages to map, not interchangeable revisions of the same file layout.

The local snapshot contains **802 Lean source modules under `src`**: 495 in `Lib`, 305 in `New`, and two top-level files. They contain 476,436 lines including comments and blank lines. All 802 are reachable from `Main` through the static module-import graph. That does not establish that every declaration is used by the final theorems.

`Lib` groups background material described by the source as known mathematics; `New` groups the argument's construction and reduction. Those labels are useful navigation, not independent certification of novelty. `GUIDE.md`, `CONTENTS.md`, `INDEX.md`, and the module introductions already supply extensive explanations.

Sources: [README](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/README.md), [reading guide](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/GUIDE.md).

## 2. The main argument is much easier to locate

The reduction now presents three inputs explicitly:

- **A:** integral source forms have short images, with controlled index.
- **B:** a limited set of translates spans almost all the target space.
- **C:** independent integral target forms satisfy a lower covolume bound.

The main inequality compares upper and lower bounds for the same covolume, with twice the index correction. The principal terms cancel, leaving a bound on the prime-sum remainder. The source lists where the cancellations occur and how the size, index, and covolume errors enter.

The visible route is `ShortAndEnough` and `LongForms` → `MainInequality` → `OneSidedBound` → the analytic criterion. This is a substantially better starting point for understanding the current argument than reconstructing it from old generated file names.

**Effect on our work:** retain the old papers as historical analyses of their pinned source. A current architecture paper should explain and verify a specific part of this existing map, including a comparison with the old interfaces, rather than present a general map as an absent resource.

Source: [main inequality and its input/error tables](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/MainInequality.lean).

## 3. A recent Landau refactor retains the leading constant

Commit `f2201365` changes the condensed analytic route from an eventual bound with unit coefficient to a bound with an explicit coefficient `A`. The resulting prime-remainder theorem retains

\[
R_{q_0}(y) \le (128\varphi(q_0)+32)y^{-1/2+\varepsilon}
\]

for sufficiently large real `y`, under its stated arithmetic assumptions. The previous version absorbed the coefficient into an extra small power of `y`. The revision carries it directly through the criterion instead.

This improves quantitative transparency. It does **not** supply a computable starting threshold merely by exposing the coefficient, and it does not by itself strengthen the ultimate zero-exclusion endpoint.

Two distinctions matter for our window study:

- The original `Deduction.zeroFree_of_rpow_window` already accepted a coefficient `C`. The coefficient-bearing interface is a recent change in the condensed route, not a newly discovered feature absent from every earlier source.
- Our old theorem concerns `Gm F` on arbitrarily late multiplicative windows. The new route bounds `primeRemainder` eventually for all sufficiently large arguments. These are different quantities and hypotheses; their equivalence has not been established here.

Sources: [actual refactor](https://github.com/leanprover-community/riemann-hypothesis/commit/f2201365d2d57b1deb4fd330aa0da37213457074), [old window theorem](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean).

## 4. Theorem C now exposes the cost of missing basis vectors

Commit `b507dc56` introduces `integral_forms_long_with_completion_cost`. Instead of immediately assuming the independent family occupies almost the whole target, it shows the penalty for completing that family explicitly:

\[
(d-n)(2x_1^2b^2+b).
\]

Here `d` is the target dimension and `n` is the number of independent forms already available. The original high-rank version of Theorem C is then obtained by bounding this completion cost.

**Why this is useful:** it exposes how a shortfall in spanning rank affects the argument. It gives us a concrete place to investigate sensitivity to incomplete recovery. Our 64-cycle recovery percentages cannot be substituted for `n/d` without a theorem connecting those different objects.

Source: [completion-cost refactor](https://github.com/leanprover-community/riemann-hypothesis/commit/b507dc564769d1107f5b0e27f34cb0ea626ba88a).

## 5. The local-density machinery is clearer, but not a direct replacement for ours

The current source separates several interfaces:

- `QuadricDisintegration` defines continuous families of measures, gives explicit chart measures, and states uniqueness at each target.
- `FibreMeasure` supplies a general relation for a measure bounded by a fiber measure; it is not itself a construction of every fiber measure.
- `FinitePlaceDensity` connects Fourier integrals, slab masses, and quadric measures.
- `SemilocalDensityBounds` bounds masses using ideal-zeta sums, without choosing a uniformizer.
- `StandardQuadrics` constructs kernels and bounds for standard forms under its rank and place assumptions.

The pointwise continuity and uniqueness machinery is directly relevant to our concern that finite neighborhood counts alone do not identify a measure at an individual target. There is already substantial infrastructure here; we should not assume a general counts-to-fiber bridge is missing.

However, `IntegralPlace` includes an integral trace-one element, an integral skew unit with integral inverse, a self-dual character normalization, and a prescribed kernel bound. The density bounds also impose rank and ideal-zeta hypotheses. Our ramified examples require a separate compatibility analysis. The complex Gram-map files are another distinct setting and must not be conflated with the nonarchimedean examples.

Searches did not locate our distinctive ramified endpoint numerals or `RamDilate` identifiers in this snapshot. That is a bounded search result, **not** evidence that no equivalent formula exists upstream or in the literature. I found no basis here for saying our results have been disproved, superseded, or automatically ported.

Sources: [quadric disintegration](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/General/Measure/QuadricDisintegration.lean), [finite-place interface](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean), [semilocal bounds](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean).

## 6. Much of the recent activity is simplification

Examples in the inspected history include removal of 21 unread fields from 13 structures, removal of the 246-line unused `Denominators` module, deletion of unused lemmas, removal of repeated type annotations in `TopFloor`, and cleanup of elaborator settings and committed Python bytecode.

These reduce maintenance and reading burden. They should not be described as independent mathematical confirmations or 61 new research findings. The 61 history records include merges and the imported readable-edition root.

Sources: [unused fields](https://github.com/leanprover-community/riemann-hypothesis/commit/f1ce1c46e207dfe46e650158917a216504635a67), [unused module removal](https://github.com/leanprover-community/riemann-hypothesis/commit/3e183e3dcfb5018e48b3de3614ebd0a28928733a).

## 7. Builds and verification have a different setup

Our archived studies used Lean 4.33.1 and Mathlib `0df444a3…`. This snapshot uses Lean **4.35.0**, Mathlib `56a00585…`, and adds Tau Ceti at `v4.35.0+patch1`. At this snapshot, the static import scan finds **no direct Tau Ceti imports under `src`**; its addition prepares dependency/cache support rather than demonstrating replacement of existing proofs by Tau Ceti results.

The configured build workflow restores an exact or compatible baseline cache, builds, rejects reported `sorry` declarations, and checks the axiom lists of five endpoint theorems. A separate publisher handles cache artifacts. The comparator configuration specifies statement comparison and nanoda, but the inspected build workflow does not itself show a comparator/nanoda step. A configuration file is not a receipt that a check ran.

The cache documentation explicitly distinguishes artifact integrity from proof checking. Its opening claim that no source files were changed describes the initial import, but is now stale if read as a description of the current branch: the source patches above occurred later. Clarifying that chronology is a concrete, narrow documentation contribution candidate.

The inherited CI configuration also expects upstream's self-hosted runner and publishing environment. Copying the branch into our fork does not create that infrastructure or give our fork a verified build.

Sources: [dependency change](https://github.com/leanprover-community/riemann-hypothesis/commit/bb636cad32b805ed97f44df485605c9fca2ec2c3), [build workflow](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/.github/workflows/build.yml), [cache documentation](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/CACHE.md).

## 8. The bibliography is useful and explicitly incomplete

`REFERENCES.md` reports 228 citations in its comparison: 66 with a confirmed location, 35 with a location confirmed at second hand, 119 with a work found but no location given, and eight not compared. Citations in 122 further files were outside that check. These are upstream's recorded classifications, not a fresh bibliography audit performed here.

This provides a focused queue for source verification. A documented match between a formal statement, its precise assumptions, and an actual theorem in the cited literature could be a useful contribution. Merely finding the title of a book or paper would not complete it.

Source: [reference audit](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/REFERENCES.md).

## Recommended order for our next research work

1. Map our old window observable and quantifiers to the new prime-remainder interface, retaining explicit constants and distinguishing eventual bounds from selected windows.
2. Compare the assumptions and normalizations of our ramified measure construction with `Place` and `IntegralPlace`, before attempting a port.
3. Examine the explicit completion-cost inequality as a possible explanation of sensitivity to lost rank; establish any connection to our recovery studies before applying their numbers.
4. Select a small upstream documentation or reference correction with a precise source basis.

No research source, manuscript, remote branch, or upstream file was changed during this review. No Lean build or mathematical reproduction was performed. Justin Candler's contribution is conceptual direction and critical questioning; AI-assisted mathematical development and review remain distinct from independent human mathematical expert review, which is outstanding for the Nous studies.
