# Ramified square dilates and the last unresolved digit

[PDF](Ramified_Square_Dilates.pdf) · [Single editable LuaLaTeX source](Ramified_Square_Dilates.tex) · [Complete ZIP](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-ramified-square-dilates/research/uriel/experiments/ramified-square-dilates/Nous_Ramified_Square_Dilates_Package.zip)

For the field ℚ(√2), the Gaussian identity Hermitian form in three variables, and the unique prime above 2, the original regular Gram-fiber measure of the original coordinate lattice at every scalar 4ᵏu² is **2 + 2/256ᵏ** for k ≥ 1 and every unit of the original valuation ring. One normalized Haar measure and admissible family realize the entire sequence. At sixteen the mass is **65537/32768**. [Original-place theorem, simultaneous realization and target-sixteen specialization](dilates/DilateEndpoint.lean)

The density splits into a primitive contribution of 15/8 and an all-divisible contribution equal to 1/16 of the preceding density when the scalar drops by a factor of two. Thus the excess over two contracts by 1/256 per square step. The quotient with r binary digits in each coefficient has uniformizer depth 2r. For k ≥ 1 the stable coefficient tail starts at r = 2k+1. For every integral unit the sharp permanent cutoff over all individual uniformizer digits is d = 4k+2. The immediately preceding odd cylinder has exact tube density two. Its two children have densities 2 ± 2/256ᵏ at the resolving depth. The finite companion result at that specified depth leaves its own pointwise mass open. [Primitive permutation](dilates/DilatePrimitivePivot.lean) · [Divisible descent](dilates/DilateDescent.lean) · [Finite lower cutoff](dilates/DilateBoundary.lean) · [Companion count](dilates/DilateCompanion.lean) · [Last odd Haar tube](dilates/DilateOddCellHaar.lean) · [Sharp stabilization on actual scalar balls](dilates/DilateStableOddAll.lean)

## Evidence

* The [independent computation](dilates/experiment.py) reconstructs exact integer counts using finite Fourier transforms and Chinese remaindering, checks ordinary histogram convolution through depth 10, and resolves four scales up to depth 18. [Saved outputs and target-sixteen strata](dilates/results.json)
* The [study replay](verification/receipt.json) records a fresh source elaboration and standalone kernel check for 108 study modules (81 inherited and 27 added here), and two rejected one-extra-vector controls. The [dependency audit](verification/dilate_dependencies.txt) records four distinct theorem closures.
* The [original import replay](verification/import_replay.txt) considered 29,137 records from 1,038 pinned dependency objects. It accepted and located 29,109, skipped 28 unsafe or partial records, and reports 239 shared declaration names. Its base is compiled Mathlib. The project-wide RH archive was outside this full local-study replay.
* The [previous release](https://github.com/nousentllc/riemann-hypothesis/tree/63c06fe44eb700e4550e4a2b70adafe09cb1ff9b/research/uriel/experiments/ramified-gram-bridge) preserves the target-four paper, earlier protocol and exact release history. The current experiment extends that bridge on a separate branch.

## Reproduction

For an offline check of the numerical data, source hashes and saved receipts, run this from the extracted study directory.

~~~sh
python3 -B verify.py
~~~

For a fresh formal run use the Lean 4.33.1 SDK at commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, a built Mathlib checkout at 0df444a360eaa60ab8c11dca51a86af692955474, and the src directory of original project revision 40e56bab026552e089d7afcfeff08d2defb9c005. Set LEAN_SDK, MATHLIB_CHECKOUT, PINNED_SRC and STUDY_CACHE to those local paths and a cache directory, respectively. The first command restores the selected, hash-pinned original proof objects from their public archives. The study sources and inventories are included in the ZIP.

~~~sh
python3 -B restore_cache.py --sdk "$LEAN_SDK" --destination "$STUDY_CACHE"
python3 -B verification/check_imports.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj"
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj" --original "$PINNED_SRC" --jobs 3
~~~

The paper embeds its original Nous PNG. Run LuaLaTeX three times on Ramified_Square_Dilates.tex in a writable directory. The release uses TeX Live 2026 with SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. The ZIP includes its PDF, that one TeX source, all study files and SHA256SUMS. [Paper checks](verification/paper.json) · [Earlier written study](https://github.com/nousentllc/riemann-hypothesis/tree/b040ed9063835e90efdecd1e4350ed35708317c0/research/uriel/experiments/uncapped-growth)

Justin Candler defined the question and approved the three proof tracks. Uriel and three AI proof workers developed the extension, formal replay and manuscript. The paper credits the original formalization and the inherited bridge.
