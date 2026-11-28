# Exact dyadic densities for a ramified Gram fiber

**Justin Candler, with AI research assistance disclosed in the manuscript · 28 November 2026**

At valuation 4k, the six-square form over the integers of Q₂(√2) has two normalized densities. They are 2 + 2/256^k and 2 − 2/256^k, selected by the parity of the √2 coefficient in the target unit. Both occur in every admissible original Gram-fiber family. The exact stable value first appears at depth 4k+2, after a common parent ball of density two.

## Paper and evidence

- [Paper PDF](Ramified_Gram_Fiber_Densities.pdf) with 41 numbered research pages, including the mathematical appendices.
- [Single editable LuaLaTeX source](Ramified_Gram_Fiber_Densities.tex) with the embedded Nous logo.
- [Full reproducibility ZIP](Nous_Ramified_Gram_Fiber_Densities.zip) · [SHA-256](Nous_Ramified_Gram_Fiber_Densities.zip.sha256).
- [Publication replay record](publication-replay.json) · [Original fourth-edition study archive](../../experiments/ramified-unit-classification/README.md).

The manuscript gives the finite recurrence, the original named-place measure comparison, the target-four valuation partition, and equality of the two pivot-chart measures on the overlap. An independent 60-address convolution checks the short coefficient derivation integrated from the editorial rewrite. The written finite argument also covers intermediate even valuations. The named original-measure Lean endpoint in this release is stated at valuation 4k.

The publication check rebuilt ten Lean study modules, including the main endpoint, verified 110 cached module records, and matched the archived replay receipt byte for byte against 1,038 original pinned imports. The scope is the local result and its dependencies. The ZIP includes the replay command, compiler and library pins, exact experiments, and the scope of the separate geometric checks. Run the included verify.py with Python 3 after extraction to repeat the offline count and integrity checks. The paper makes no priority claim for the density formula.
