# How much local mass survives near zero?

[Full paper](Uncapped_Growth.pdf) · [Single-file LuaLaTeX source](Uncapped_Growth.tex) · [Complete package](Nous_Uncapped_Growth_Package.zip)

For each admissible CM extension, nondegenerate Hermitian form of rank M ≥ 3, coordinate basis, standard local Haar measures, original admissible Gram families and nonzero scalar target β, one **unique least positive integer N** generates the entire positive support of the original finite-place product P(a). For positive integers a, **P(a)>0 iff N divides a**. A single positive constant c gives **P(a) ≥ c a^([F:Q](2M−2)) on all of that support**. The original extra assumption of nonzero measures at β follows from the local theorem. These statements are existential for general input. [Exact support](global/OptimalSupport.lean#L53) · [All-multiples theorem](global/UncappedGrowth.lean) · [Previous capped study](https://github.com/nousentllc/riemann-hypothesis/tree/e3bf793943ea2f2eab748816b974a8a0c11bdbbe/research/uriel/experiments/parallel-growth)

## The three investigations

1. **Local geometry.** The original five-variable theorem supplies a nonzero isotropic vector of the trace form over every finite completion. The nondegenerate matrix supplies a second isotropic direction and an affine scalar coordinate. Averaging translations along this direction gives a uniform tube estimate for the original coordinate Haar measure. The regular-target set formula transfers it to the original lattice mass for every sufficiently small nonzero target. The support axiom forces the assigned singular member to vanish. Lean proves discontinuity at zero. [Local derivation and original-source anchors](local/analysis.md) · [Haar estimate](synthesis/CoordinateFloor.lean) · [Original-family floor](local/OriginalFloor.lean) · [Discontinuity](local/SingularJump.lean)
2. **Global growth.** The actual exceptional factors at all places above one rational prime move together. A positive eventual floor for each such product is necessary and sufficient for uncapped growth at the selected base. The first positive shell at each place and the finitely many necessary valuation thresholds yield the least common multiple prescribing the exact support. The denominator control shows why N can matter. [Global derivation](global/analysis.md) · [Prime-block criterion](global/ExceptionalPrimeCriterion.lean#L61) · [Exact support](global/OptimalSupport.lean)
3. **Gaussian dyadic density.** At target (2^k u)^2 for odd u the original lattice mass equals 1−1/(4·16^k). Every normalized finite count before depth 2k+2 equals one, and every count at or beyond that depth equals the displayed value. The minimum over all positive square multipliers is 3/4, attained for odd multipliers. The zero tube has ratio one at every depth, while the assigned zero measure vanishes. [Dyadic derivation](dyadic/analysis.md) · [All-depth count](dyadic/SquareDepth.lean) · [Original-family equality](dyadic/GaussianDilates.lean) · [Sharp floor](dyadic/GaussianSharp.lean)

For the coordinate six-square example over all primes the paper derives, in ordinary mathematics, the sharp relative infimum ∏_(p≡3 mod 4)(1+p⁻²)⁻¹. Its value is between 0.86723376 and 0.86724245, and no finite multiplier attains it. A sequence supported on progressively many inert primes approaches it. Jacobi's exact integer representation formula provides a second derivation. This all-prime calculation is a written proof with independent finite checks. The general Lean theorem establishes growth on the support without computing the best coefficient. [Exact computations](synthesis/gaussian_product.json) · [Authors' proof of Jacobi's formula](https://people.math.carleton.ca/~aalaca/pubs/aa2007-6.pdf)

## Reproduce the results

From the extracted directory run the offline Python 3.11+ check. It compares freshly generated numerical results with the archived JSON and checks source hashes against the proof receipts.

~~~sh
python3 -B verify.py
~~~

The original source is pinned at 40e56bab026552e089d7afcfeff08d2defb9c005. The checked Lean toolchain is 4.33.1, revision 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The compiled Mathlib checkout is revision 0df444a360eaa60ab8c11dca51a86af692955474. For a fresh proof replay, set LEAN_SDK to the extracted SDK, MATHLIB_CHECKOUT to the built Mathlib checkout, PINNED_SRC to the original project's src directory, and STUDY_CACHE to a writable directory.

~~~sh
python3 -B restore_cache.py --sdk "$LEAN_SDK" --destination "$STUDY_CACHE"
python3 -B verification/check_imports.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj"
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj" --original "$PINNED_SRC"
~~~

The study and inherited source modules are bundled. The 1,038 original dependency binaries, the full original repository, the SDK and Mathlib are external verification inputs. All 1,038 selected original source blobs were checked against the pinned Git tree. The selected preservation archives have recorded digests. The bulk replay accepted and located 29,109 project declarations, with 28 unsafe or partial entries skipped and 239 shared name occurrences. Of the original objects, 538 match the separate MIT binary manifest byte-for-byte and 500 differ. We have not determined the causes of those differences. The trusted base includes compiled Lean and Mathlib. This study did not build the full RH formalization. [Original inventory](original_imports.json) · [Bulk replay](verification/import_replay.txt) · [Study replay](verification/receipt.json) · [Dependency checks](verification/dependencies.txt) · [Preservation cache](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/main/verification/CACHE.md) · [MIT archive](https://math.mit.edu/~drew/grh/)

The ZIP includes the editable TeX, compiled PDF, code, experiment data, source selection, proof receipts, checksums, and a restorable study Git bundle. The standalone source embeds the Nous PNG. Run LuaLaTeX three times in a writable directory. The published build uses TeX Live 2026 with SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. The ZIP itself is published alongside the paper on the research branch.

Justin Candler directed the research. Uriel and three parallel AI research workers developed, tested and integrated the new mathematical arguments. The original authors, Mathlib, verification archives and prior publications are credited in the manuscript.
