# How often is the local product large?

**Follow-through.** The [uncapped-growth study](../uncapped-growth/) subsequently characterizes the positive support and proves a uniform lower estimate on that support for the rank-at-least-three problem. The rank-two scaling control below still applies to its own example.

Three concurrent studies of the rank-one finite-place growth bound and its Siegel–Weil consumer. [Paper](Parallel_Growth.pdf) · [Single-file LuaLaTeX source](Parallel_Growth.tex) · [Integrated theorem](verification/ProgressionEndpoint.lean) · [Elaborated dependency and endpoint audit](verification/EndpointAudit.lean).

## The mathematical results

1. **Bounded gaps.** For each admissible input with source rank M ≥ 3, nonzero scalar β and nonzero finite fiber measures, there are fixed positive integers N,Q and a positive real c such that the original product of dilated Gram masses at β is at least c times a to the power $`[F:\mathbb{Q}](2M-2)`$ for **every** a=N(1+Qj), j ≥ 0. Every interval (k,k+NQ] contains such a witness. The wait NQ is attained inside the chosen progression. Other admissible witnesses may occur sooner. The proof does not compute N,Q,c for a general input. [Growth theorem](verification/ProgressionGrowth.lean#L56) · [Waiting time](verification/ProgressionGeometry.lean).
2. **Normalization.** For a fixed positive archimedean weight, the abstract comparison inequalities force the scalar to equal one precisely when the product divided by the analytic error scale is unbounded on the common allowed test set. We prove the original rank-one SWMeas conclusion with the progression substituted, and separately with the pinned sparse growth theorem. Both endpoints have the original elaborated theorem type. The new route uses the progression and omits the old growth theorem. On the zero-measure branch the measure identity with multiplier one holds without uniqueness of the multiplier. [Sharp comparison and countermodels](verification/GrowthConsumer.lean) · [Original measure inputs](verification/OriginalGrowthConsumer.lean) · [Consumer](verification/RankOneConsumer.lean) · [Substitution](verification/ProgressionEndpoint.lean) · [Trace](consumer.md).
3. **Larger multiplier classes.** One can choose N and a finite set B before the valuation cap profile H. For every fixed H there is a positive coefficient c(H) working for *every* positive t such that ord_v(t) ≤ H(v) for v in B, at the dilation Nt. Unit multipliers already include every residue coprime to the exceptional ideals. This controls the valuation of t, leaving the fixed N untouched. The neighboring rank-two four-square count has stabilized density 3/4^k at 4^k. It proves the failure of a cap-independent conclusion from scaling alone. Whether the full rank-at-least-three hypotheses give a uniform lower bound with no cap remains open in this study. [Capped theorem](verification/CappedGrowth.lean) · [Local inequality](verification/ExceptionalDilation.lean) · [All-depth control](verification/FourSquareControl.lean) · [Evidence and qualifications](exceptional.md).

## Numerical controls and capacity

Standard-library computations check 37,008 small progression cutoffs, five complete exceptional residue periods, 25 rank-two target/depth pairs and eight rank-three comparisons. In the rational example B={2,3}, out of 36 multipliers, six are 1 modulo 6, twelve are units at both primes, and twenty-four meet caps of one at both. These B,N,Q examples illustrate the witness classes. The generic original theorem chooses its own B and N. [Witness data](witness_checks.json) · [Parity and valuation data](exceptional_experiment.json).

Three AI research workers ran concurrently on distinct mathematical questions. A fourth coordinating worker integrated the proofs, checked the sharp cutoff geometry and the deployment of the original source, and built the release. This is demonstrated capacity in this run. Worker agreement does not constitute independent model replication.

## Reproducing the checks

The ZIP includes one TeX, its PDF with embedded Nous branding, the study and inherited proofs, key original-source files, compiled-proof receipts, scripts, data, checksums and a restorable Git bundle. It omits the large Lean distribution, Mathlib build and original dependency binaries. After extraction the quick checks require only Python 3.11+.

~~~sh
python3 -B witness_checks.py
python3 -B exceptional_experiment.py
python3 -B verify.py
~~~

For the full audit use Lean 4.33.1 (compiler revision 819816b2e0a3bf405af45ae5c7af2491d8f5bee6), a built Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474, and the **src directory** of the original project at 40e56bab026552e089d7afcfeff08d2defb9c005. Set LEAN_SDK, MATHLIB_CHECKOUT, PINNED_SRC and STUDY_CACHE to these three locations and an empty local cache destination, respectively.

~~~sh
python3 -B restore_cache.py --sdk "$LEAN_SDK" --destination "$STUDY_CACHE"
python3 -B verification/check_imports.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj"
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --original "$PINNED_SRC" --objects "$STUDY_CACHE/obj"
~~~

The bulk check reads the original dependency objects, gathers their project declarations and replays them through Lean's kernel in an environment initialized with Mathlib. The module-specific replay authenticates all 1,863 source blobs and compiled input objects, freshly compiles four original source files, four inherited finite-count modules, and the new mathematical and dependency-audit modules. It rechecks each of those rebuilt modules with the standard leanchecker, audits the recorded axioms and checks the two actual proof routes. [Bulk receipt](verification/import_replay.txt) · [Isolated build receipt](verification/receipt.json) · [Source and object inventory](original_imports.json).

The cache contains a subset of the original-source preservation build. All selected public archive SHA-256 digests are committed here and were checked. Of the 1,863 unpacked object hashes, 1,017 also match the independent MIT object manifest byte for byte. The other 846 have distinct binary hashes. The bulk replay accepted and located 43,467 declarations in the kernel environment. Lean's replay implementation skips unsafe or partial declarations, accounting for 31 of the 43,498 distinct project entries. The collection also encountered 390 shared name occurrences. Its trusted base includes the pinned compiled Mathlib. We did not rebuild the full RH proof, or determine the cause of the cross-build binary differences. [Preservation cache](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/main/verification/CACHE.md) · [MIT verification archive](https://math.mit.edu/~drew/grh/).

Compile the single paper source with LuaLaTeX three times in a writable directory. The original Nous PNG is embedded after the document. The release uses TeX Live 2026 with SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1.

## Sources and collaboration

[Original growth](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneLocalDensitiesProductConverges.lean#L262-L382) · [Original normalization](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/AutomorphicTheory/ThetaDilations/SwOne.lean#L22-L101) · [Earlier arithmetic study](https://github.com/nousentllc/riemann-hypothesis/tree/609877747df336e925a39085acf02c8f994f66a3/research/uriel/experiments/rank-one-growth) · [Target-four release](https://github.com/nousentllc/riemann-hypothesis/tree/b4d12e0825d2191f38fdfb5e97b327c8c8ad1b3d/research/uriel/experiments/gaussian-target-four).

Justin Candler directed the investigation. Uriel and three parallel AI research workers developed and tested the new results. The original formalization, the independently maintained verification archives and Mathlib are prior work.
