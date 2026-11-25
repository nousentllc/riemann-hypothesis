# Three quarters at one

The rank-one Gram-fiber measure at the scalar target one assigns the integral Gaussian lattice mass **3/4** at the rational place above two. The field is Q(i), the basis is (1,i), and the Hermitian matrix is the three-dimensional identity. The equality holds for every standard Haar measure and every admissible family in the pinned source. Lean also proves that both exist.

| Claim | Formal evidence |
|---|---|
| Ordered six-square counts at **all** depths including zero | [count_all](verification/Shallow.lean), [count_late](verification/AllDepth.lean), [unit-square action](verification/FiniteCounts.lean) |
| CM field, explicit trace matrix 2I, original tensor trace | [isCM](verification/GaussianField.lean), [trace_coords](verification/GaussianTrace.lean) |
| Actual local completion, integer cylinders, equal Haar volume | [DyadicLocal](verification/DyadicLocal.lean), [cyl_mass](verification/Cylinders.lean) |
| Exact measured tubes of the six-coordinate quadratic map | [tube_three_quarters](verification/Tubes.lean) |
| Identification at a single point by compact tests and regularity | [contact](verification/Contact.lean), [local_mass_from_tests](verification/Nearby.lean), [small_cylinder](verification/Neighborhoods.lean) |
| Original lattice, Hermitian target and literal extended measure | [target_one_mass](verification/Endpoint.lean) |
| Existence of a normalized Haar measure and an original family realizing 3/4 | [realized_unconditionally](verification/Existence.lean) |

At depth zero the count is one. At depth one the count is 32. For every r at least two the count is three quarters of (2^r)^5. At depth three every fine target reducing to one modulo eight has the same count as target one, and this remains true at every higher depth.

The original admissibility and Haar conditions are the only hypotheses about measures in the universal theorem. Its target, lattice, and family predicates expand to the pinned hermScal, latV, and IsGramFib. The unconditional existence statement has no arguments. The original existence theorem supplies the family by disintegration.

## Why counting the children of a single parent fails

At modulus four there are 768 solutions and the normalized count is 768/1024. At modulus eight there are 24,576 solutions. At modulus sixteen exactly half the level-three parents send **all 64** vector lifts to one. The others send every lift to nine. A parent with first entry one and the other five zero sends all 64 to one. Replacing its first entry by three sends all 64 to nine. Unit scaling establishes uniformity after summing across parents.

## Reproduction

Run the standard-library checks in the extracted study directory.

~~~sh
python3 -B experiment.py
python3 -B verify.py
~~~

The independent checks cover every level through modulus 1,024, all 266,305 ordered vectors across moduli 1, 2, 4 and 8, and 255 square-class targets across levels three through ten. The all-depth conclusion is a Lean theorem.

For a clean Lean replay use the Lean 4.33.1 distribution and a built checkout of Mathlib at the commit below. Set the two environment variables to the respective installation directories.

~~~sh
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT"
~~~

This builds 51 pinned project modules and 13 study modules in an empty temporary directory, verifies source hashes, replays each object with Lean's kernel, and compares the evidence with [the receipt](verification/receipt.json). The release audit replayed the compiled objects individually. The six recorded axiom closures use propext, Classical.choice and Quot.sound. The bundled replay supports an optional existing-build directory. The full global project and Mathlib itself were outside this build.

The manuscript compiles from its single TeX file. The Nous PNG is embedded. Run LuaLaTeX twice in a writable directory with the packages named in the preamble. Set SOURCE_DATE_EPOCH=1795551886 and FORCE_SOURCE_DATE=1 to reproduce the release timing metadata.

## Provenance and collaboration

[Original source commit](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Previous dyadic study](https://github.com/nousentllc/riemann-hypothesis/tree/0cce5c50f1468cc7519e6eb2e18386556c4cfdd8/research/uriel/experiments/dyadic-fiber) · [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).

The [manifest](manifest.json) distinguishes exact upstream imports from study modules. The two additional source files in references document the pinned local-ring and lattice arguments adapted for the concrete specialization. The local square-chart proof follows the original calculus argument. Local compactness here transports directly from the dyadic field.

Justin Candler directed the investigation. Uriel, the AI research assistant, developed the local formalization, ran the verification and independent computations, and prepared the manuscript. The pinned formalization and Mathlib are prior work.
