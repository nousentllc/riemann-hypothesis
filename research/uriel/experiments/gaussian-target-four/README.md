# The Gaussian fiber at four

At the place of **Q** above two, use the identity Hermitian form on three Gaussian entries in **Q(i)**, the integral basis (1,i), and additive Haar measure normalized to give the ring of integers volume one. For **every** admissible original Gram-fiber family, its measure at the scalar Hermitian target four gives the full integral lattice mass **63/64**, the primitive region **15/16**, and the all-even sublattice **3/64**. Here “all even” means that all six rational-basis coefficients are in twice the local integer ring. Primitive means that the integral vector has at least one odd coefficient. Lean also supplies a normalized measure and an admissible family realizing all the equalities simultaneously.

[Paper (PDF)](Gaussian_Target_Four.pdf) · [Single-file LuaLaTeX source](Gaussian_Target_Four.tex) · [Original-fiber theorem and witnesses](verification/FourEndpoint.lean#L106) · [All-depth count theorems](verification/FourCounts.lean) · [Clean kernel replay receipt](verification/receipt.json).

## The two-depth shift

Write M = 2^r, and divide each finite count by M^5. At r = 0 the parity convention uses the unique least representative zero. Its unique box still represents the whole integral lattice, so the analytic parity correspondence starts at r = 1.

| Depth r | Primitive | All even | Total |
|---|---:|---:|---:|
| 0 | 0 | 1 | 1 |
| 1 | 31/32 | 1/32 | 1 |
| 2–3 | 15/16 | 1/16 | 1 |
| ≥ 4 | 15/16 | 3/64 | 63/64 |

At depth k+2, an even vector modulo 4m halves uniquely to a vector modulo 2m, where m = 2^k. Its reduction modulo m has squared norm one. Each solution modulo m has two lifts per coordinate. Thus the even count equals 64 times the target-one count two levels earlier. Dividing by (4m)^5 introduces the factor 64/4^5 = 1/16. The two shallow target-one densities are both one. At every depth k ≥ 2, the previously certified density at one is 3/4. This is the source of the 3/64. At the regular original fiber, Lean also proves that the even mass at four equals exactly one sixteenth of the full mass at one **for the same family and normalization**.

At modulus sixteen the counts are **983,040 primitive + 49,152 all even = 1,032,192**. The deficit from 16^5 is 16,384. Each solution at one modulo four produces 64 all-even vectors at four modulo sixteen. The target-one shortfall of 256 therefore accounts for the whole deficit.

## Proof map

| Obligation | Source |
|---|---|
| Certified finite histograms through modulus 32, then unit-square scaling and a double partition above 32 | [FourBase](verification/FourBase.lean), [FourLift](verification/FourLift.lean#L64) |
| Partition of the actual finite solution type, the halving bijection, and the exact 64-fold lift | [FourEven](verification/FourEven.lean#L52) |
| Every natural depth, including the transition at sixteen and the tiny moduli | [FourCounts](verification/FourCounts.lean), [prior theorem at one](verification/Shallow.lean) |
| Compatibility of fine digits with parity, reindexing by the Gaussian coordinates, exact restricted and full tube measures | [FourTubes](verification/FourTubes.lean) |
| Original trace matrix, scalar Gram map and regular-family predicate | [GaussianTrace](verification/GaussianTrace.lean), [prior endpoint](verification/Endpoint.lean) |
| Compact-test disintegration with an explicit restricted coordinate set, and arbitrarily small positive-volume test cylinders | [FourContact](verification/FourContact.lean#L96), [FourNeighborhood](verification/FourNeighborhood.lean) |
| Topology of the original even lattice, three measure evaluations, same-family transfer and unconditional existence | [FourEndpoint](verification/FourEndpoint.lean), [inherited existence](verification/Existence.lean) |

The Lean route to the primitive count subtracts the even count from an independent all-depth total. The manuscript also derives the primitive count directly by fixing four odd positions and counting odd square roots. The latter argument is presented on paper and its finite consequences are independently tested. The even-fiber calculation uses the compact-open indicator of the actual even sublattice. The resulting equality is about this set and this family. No universal change-of-variables theorem for arbitrary measured sets is asserted.

## Independent checks

The [standard-library experiment](experiment.py) checks both parity classes by exact histograms through modulus 1,024. It enumerates all 266,305 vectors across moduli 1, 2, 4 and 8, computes the sibling distribution at modulus sixteen, verifies the unit-orbit obstruction at modulus thirty-two, and checks the odd square-root multiplicities through depth ten. [Recorded results](experiment.json).

At modulus eight, 15,360 primitive parents feed each of the two children 4 and 12 modulo sixteen. Among the all-even parents the corresponding counts are 768 and 1,280. Each parent feeds all 64 of its lifts to one child. The comparison at twelve is finite evidence. The unbounded Lean statement in this release is about four.

## Reproduction

From the study directory run the two portable checks.

~~~sh
python3 -B experiment.py
python3 -B verify.py
~~~

For a fresh kernel replay install the Lean 4.33.1 distribution and a built checkout of Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. Set LEAN_SDK to the distribution root and MATHLIB_CHECKOUT to the checkout root, then run

~~~sh
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT"
~~~

The replay compiles 51 pinned project modules, 13 unchanged target-one modules, and eight new modules in a fresh temporary directory. It calls leanchecker on all 72, audits eleven declaration closures, and compares its output to the published receipt. The recorded axiom sets consist of propext, Classical.choice and Quot.sound. The replay uses the built Mathlib dependency. It covers the selected project imports, with the full global proof outside its scope. The [manifest](manifest.json) records the source hashes, import graph, pinned blobs and eleven audited declarations.

To build the paper, run LuaLaTeX at least twice on Gaussian_Target_Four.tex in a writable directory with the packages in its preamble. The single source embeds the original Nous PNG. The release used three runs, TeX Live 2026, SOURCE_DATE_EPOCH=1795551886 and FORCE_SOURCE_DATE=1. The archive includes the PDF and editable TeX at the study root, all proof and test files, a Git bundle, and SHA256SUMS.

## Provenance and collaboration

[Original source at 40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Predecessor at 49feb57d](https://github.com/nousentllc/riemann-hypothesis/tree/49feb57ded97dfd384aae1c86538df32fea856a9/research/uriel/experiments/gaussian-target-one) · [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).

Justin Candler directed the investigation and specified the decomposition, link to target one and end-to-end audit. Uriel, the AI research assistant, developed the local proof, performed the independent computations and verification, and prepared the paper and package. The pinned formalization and Mathlib are prior work.
