# The integers behind the mass bound

A witness-level audit of the finite-place lower estimate used to normalize a rank-one Siegel–Weil measure, with an independent six-square calculation. The study uses the original Lean revision `40e56bab026552e089d7afcfeff08d2defb9c005` and is additive to the research branch history. [Pinned growth proof](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankOneLocalDensitiesProductConverges.lean#L262-L382)

## Read the paper

[Download the PDF](Rank_One_Growth.pdf) or [open the single LuaLaTeX source](Rank_One_Growth.tex). The Nous PNG is embedded in the TeX. The release ZIP contains both files, all computations, the original source witnesses, the Lean replay and checksums.

## Findings and scope

1. The original proof chooses positive integers N and Q once and supplies the actual integer N(Q+1)^k for each cutoff k. The integer N clears the target denominator and preserves a positive patch at each exceptional finite place. Multiplication by Q+1 preserves the baseline normalized density except at a fixed finite set of good places. Matched with the analytic estimate at the identical integer, the exponent gain D(M−2) forces the comparison scalar to be one on the nonzero branch.
2. Retaining the original uniform estimate before it is weakened to a half gives a mathematical corollary. With the exceptional set chosen for that full estimate, all integers N(1+jQ) satisfy a common positive lower bound, with spacing NQ. The product comparison on prime ideals, ideal avoidance and the integer arithmetic were kernel-replayed. The substitution into the full original measure development is proved on paper. A numerical N and Q depend on the input field, form, target and local positive-mass witnesses.
3. For the independent six-square counting model all 2,599 finite density comparisons matched. On odd dilations the elementary bound is 2/9. The sharp infimum lies between 0.671276669092272880 and 0.671277340369020467. Its Euler product, a sequence approaching it, and the proof of nonattainment are in the paper. Of 50,000 odd integers through 100,000, the unique minimizer was 39,501. Its normalized mass is within 0.592 percent of the infimum. This uses an explicit congruence normalization. A formal comparison with the original dyadic Gram-fiber measure remains outstanding.

## Replay

Use Python 3.11 or later with ordinary assertions enabled. The programs run on a CPU and have no third-party Python dependencies. In the extracted directory run

~~~sh
python3 -B experiment.py
python3 -B sharp.py
python3 -B verify.py
~~~

The first two recompute and compare with the archived JSON. The third checks 12 original Git blobs, five verbatim theorem bodies, the locally archived graph edges and the identity of the modules in the replay receipt. For comparison with independent copies use the optional arguments to verify.py, for example

~~~sh
python3 -B verify.py --repo ../riemann-hypothesis --graph ../alp-declaration-graph-used-by-rh.json.gz
~~~

The optional checkout must contain the pinned source commit. The graph can be downloaded from the URL in graph.json and is checked against the full compressed-file digest. Its edges are publisher-reported references in elaborated declarations. [Compiled graph archive](https://photos.proofsandreasons.io/alp-graph/rh/alp-declaration-graph-used-by-rh.json.gz)

To repeat the five-module kernel replay, point the following command to Lean 4.33.1 and Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474 with compiled dependencies. Use the same platform/toolchain to match the recorded compiler banner exactly.

~~~sh
python3 -B verification/replay.py --sdk /path/to/lean-4.33.1 --mathlib /path/to/built-mathlib
~~~

The three original modules, original declaration excerpts in Inputs.lean, and new conditional lemmas in Progression.lean are distinguished by verify.py. The replay prints the axioms of all four new lemmas. Full elaboration and kernel replay of the entire RH development were outside this run's available project build. The larger original modules are included for source inspection. No inference API or paid calls were needed.

For the single-file manuscript, use LuaLaTeX with the packages named in its preamble and a writable directory. Run it three times for stable page references. The release uses TeX Live 2026, SOURCE_DATE_EPOCH=1795551886 and FORCE_SOURCE_DATE=1. Comparing the regenerated PDF bytes requires the matching TeX installation and fonts.

## Evidence files

| File | Contents |
|---|---|
| sources.json and source/ | Original paths and revision, Git blob and SHA-256 checks, UTF-8 originals |
| graph.json | Original use-in-body route and provenance |
| experiment.json | Congruence counts, partial products, coarse envelope, shrinking-floor control, composite-base and rank-boundary examples |
| sharp.json | Certified infimum intervals, rational finite search, all strict records, independent divisor cross-checks |
| verification/receipt.json | Compiler and kernel replay output, hashes, dependency revisions, axiom reports |
| SHA256SUMS and study-history.bundle | Additional files inside the ZIP for integrity checks and standalone Git recovery |
