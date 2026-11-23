# Reproduce the weighted orbit experiment

Run `python3 -B verify.py` from this directory (standard Python 3.9 or later). The programs use integer comparisons for all decisions, including primality, powers, density inequalities and ceilings. The reported masses and some displayed thresholds are floating-point approximations. The verifier regenerates the four saved numerical records and compares primary results with independent calculations. A typical CPU run takes seconds.

| Question | Primary files | Independent checks |
|---|---|---|
| Three finite arithmetic hosts, the eligible prime, window extrema, tile flags, membership charges and threshold | [experiment.py](experiment.py), [results.json](results.json) | [independent_check.py](independent_check.py), [oracle.json](oracle.json) for the two tile examples |
| Exact two-coset relation on an orbit of size 2^64 | [index_two.py](index_two.py), [index_two.json](index_two.json) | [index_two_certificate.py](index_two_certificate.py), [index_two_independent.json](index_two_independent.json) |
| Design, timing of the hypotheses and test constant | [Study design](DESIGN.md) | Full-count results and sensitivity controls are reported in the manuscript |
| Prime class, source constructors, canonical representative, explicit rank and modulus | [Host trace](HOST.md) | Primality and modular-order certificates in the programs and the host formalization |
| General source-level orbit lemmas and replay instructions | [OrbitBudget.lean](lean/OrbitBudget.lean), [replay guide](lean/README.md) | [Kernel receipt](lean/verification.json) |

The host supplement proves the four named host existence statements and identifies the Frobenius choice with the Artin projection at a prime coprime to the conductor. The incidence supplement proves the exact double count for cyclic windows. [Host Lean source](host/ConcreteOrbitHost.lean) · [Host replay](host/host_verified.json) · [Incidence source and replay guide](incidence/README.md) · [Pinned source hashes](SOURCE.json)

### Formal replay

The original mathematical source is [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005). The replay programs import helpers and authenticate source/object inventories from the [earlier retained-host experiment at 9ac7e1b](https://github.com/nousentllc/riemann-hypothesis/tree/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host). Follow its REPRODUCE.md to obtain the original source, Lean installation, matching Mathlib installation and original objects. Use a checkout at **9ac7e1b** as the helper checkout even if you access this study from the branch based directly on research/uriel. Each supplemental module has a separate replay record. None is a new verification of the RH entry point.

### Reading the measurements

The small examples use an index-one distinguished subgroup plus an extra four-class control. The compressed example uses the proof's own nontrivial subgroup and the prescribed exact 4:3 shares. All four use a nonempty arithmetic prime filter containing exactly 3 and fix the experiment constant Cb=1. The pointwise local-good failure and Boolean budget failure are separate facts. See the manuscript for the full constant threshold, selected-host limitations and rank obstruction.

The PDF builds with LuaLaTeX in two passes from its adjacent .tex file. Relative evidence links resolve when the manuscript and the evidence folder stay together. The .tex compiles independently of the data files; local launch links depend on the PDF viewer. The ZIP's SHA256SUMS lists the other files in the package.
