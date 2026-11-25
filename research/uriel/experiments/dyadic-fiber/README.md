# One more dyadic digit

This study follows the finite-place density in the rank-one Siegel–Weil normalization proof to the prime two. The field is the rational numbers, the CM field is the Gaussian rationals, the basis is 1 and i, and the Hermitian matrix is the identity in dimension three. The preceding study obtained 3/4 from independent six-square counts. Here the question is whether this value survives the source's choice of input, target and fiber measures. [Previous study](https://github.com/nousentllc/riemann-hypothesis/tree/609877747df336e925a39085acf02c8f994f66a3/research/uriel/experiments/rank-one-growth)

[Read the 33-page paper](Dyadic_Fiber.pdf) or [open its single LuaLaTeX source](Dyadic_Fiber.tex). The release ZIP includes both files, the embedded Nous logo, all numerical data and programs, original proof sources and the Lean replay record.

## Main results

- The original scalar target coordinate uses half the algebra trace. For a scalar in a quadratic algebra this is exactly the scalar. The source's rank-one target map sends the normalized scalar Haar measure to its prescribed Hermitian target measure.
- The original constant-density lemma asks for equality on all odd targets when centered at 1. The two children have densities 3/4 and 5/4; the parent average is one. Its hypothesis fails in this instance. We kernel-replayed a localized proof with the same source Gram-fiber measures on an arbitrary regular open neighborhood.
- Mathematically specializing on 1 + 4Z₂ gives 3/4 at 1. More generally the standard lattice mass at a nonzero integral s = 2^t u is 1 − χ₄(u)/4^(t+1). The proof uses primitive counts mod eight, exact binary lifting, the all-even recurrence and extension from cylinder measures. The paper identifies the remaining steps for a single end-to-end numerical Lean theorem.
- At zero the continuous representative of the counting density has value one and every shrinking tube has average one. The support condition in the original definition of a regular fiber family forces the singular-target measure to be zero. That statement was checked directly in Lean, including the rank-one zero case.
- A fresh rational calculation covers all 100,000 positive dilations. It finds the unique overall minimum at 39,501 and the unique even minimum at 79,002, with ratio 21/16. The all-integer infimum in the six-square model equals the previously certified odd infimum.

## Reproduction

In the extracted directory run the following commands with Python 3.11 or later and ordinary assertions enabled. They do not require a network connection or a paid inference service.

~~~sh
python3 -B experiment.py
python3 -B dilations.py
python3 -B verify.py
~~~

The first recomputes every one of 4,094 residue bins through modulus 2,048. It also runs the direct tuple checks through modulus eight, the next-bit check on 258,048 primitive tuples, normalization controls, ten resolution comparisons and 8,128 variation checks. The second evaluates the signed odd divisor sum and the dyadic multiplier with exact rational comparisons. The third cross-checks original source and replay hashes plus saved graph locations. To compare against external copies of the artifacts, supply the optional paths.

~~~sh
python3 -B verify.py --repo ../riemann-hypothesis --mathlib ../mathlib4 --graph ../alp-declaration-graph-used-by-rh.json.gz
~~~

The original archive revision is 40e56bab026552e089d7afcfeff08d2defb9c005. Original module paths, Git blob IDs and SHA-256 sums are in sources.json. The previous graph archive URL and digest are in anchors.json. Mathlib sources used to interpret the completion and finite-measure uniqueness are pinned in mathlib.json. [Original local mass comparison](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneLocalDensityAlmostAll.lean#L29-L183)

## Formal verification

Supply Lean 4.33.1 and a built Mathlib at commit 0df444a360eaa60ab8c11dca51a86af692955474. The script starts in a clean temporary directory and re-elaborates and kernel-replays each of the 23 original modules and three new modules. The compiler output, axiom lists, kernel replay messages, hashes and toolchain are archived. The exact receipt comparison expects the same compiler banner and platform; all proof source is available for other compatible installations.

~~~sh
python3 -B verification/replay.py --sdk /path/to/lean-4.33.1 --mathlib /path/to/built-mathlib
~~~

Coordinates.lean checks the singular support consequence in the original IsGramFib definition, the Gaussian identity form in coordinates, the scalar half trace, and the compatibility of integral and field completion transport. DyadicArithmetic.lean checks the primitive binomial table, lifting algebra, recurrence implication and the measure extension lemma. LocalMassOnOpen.lean uses the original disintegration and coordinate lemmas, explicitly accepting the local-ring, compact-open lattice, trace-coordinate and local tube hypotheses. The concrete all-depth count-to-Haar specialization is proved on paper and tested independently. The full RH development was not rebuilt.

## Release contents

| File | Contents |
|---|---|
| experiment.json | Finite level counts, primitive table, sibling densities, perturbation controls and resolution diagnostics |
| dilations.json | Exact rational minima among odd, even, and all positive inputs through 100,000 |
| sources.json and source/ | The 28 pinned original modules and their identities |
| anchors.json and mathlib.json | Declaration-level graph locations and independent Mathlib sources |
| verification/ | Three new Lean files, fresh-build replay and its receipt |
| SHA256SUMS and study-history.bundle | Additional ZIP members for integrity and recovery |

The single TeX embeds the PNG used on the title page. Run LuaLaTeX three times for stable references, using a writable working directory. The release used TeX Live 2026 with SOURCE_DATE_EPOCH=1795551886 and FORCE_SOURCE_DATE=1.
