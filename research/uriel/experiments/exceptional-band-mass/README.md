# Exceptional bands and positive prime mass

The experiment traces what survives when the original exceptional-integer test fails, then measures how much positive mass lies inside equal-width bands of an actual Dirichlet-character prime sum.

**[Read the research paper](Exceptional_Bands_and_Prime_Mass.pdf)** · **[Single editable LuaLaTeX source](Exceptional_Bands_and_Prime_Mass.tex)** · **[Evidence and scope by claim](CLAIMS.json)** · **[Provenance and verification](PROVENANCE.json)**

## Findings

* The original cutoff checks every exceptional integer up to an ambient ceiling. The local sum uses integers strictly below its own cutoff. Even for active integers, earlier cohomological estimates retain a quantitative bound. In the notation of the paper, the published dimensionless exponent is 1/2. With the other source hypotheses in place, strict exponents below 11/20 suffice for the rounded moving-field bound, below 3/5 for the earlier prime-pair version, and below 4/5 for a fixed odd reference field. These are written layer-level deductions. The exact arithmetic and formal verification scope are in the [original-source audit](evidence/upstream/sources.json) and [Lean receipt](evidence/upstream/kernel.json).
* For at most R arbitrary exceptional labels, B = Ct/η > 1 and power-window exponent λ > 1, the sharp generic guaranteed search budget is J = λ(λB)^R. For λ = 2 this halves the sufficient budget in the pinned selector. The [geometry code and proofs](evidence/geometry/) include half-open endpoints, adversarial integer labels, partial overlap and clean subwindows.
* On [256,4096], a band [s,2s] always has 25% of the logarithmic width. For the actual modulo-four sum at square-root normalization, the exact continuous search encloses its share of total positive mass between extrema of 4.77256460% and 47.48374447% (rounded). The largest share among four aligned bands occurs on [1024,2048], while the unique pointwise peak at 487 falls in [256,512]. The [full data](evidence/primes/results.json) include both normalization exponents, the optimizer enclosures and independent quadrature controls.
* If the true scalar sum is bounded at both ends of a hole, its ramp formula prices the missing area through downward prime-power slope jumps and a smooth principal correction. A cubic log-width term and a quadratic lattice correction give a sufficient mass bound on a collection of narrow holes. This is a written theorem with [finite sign and curvature checks](evidence/bridge/results.json). The source ablation alone does not supply both endpoints, sufficiently narrow holes, or the identity of a realized arithmetic exception.

## Run locally

With Python 3.11 or newer, from this directory:

```sh
python3 -B evidence/reproduce.py
```

This verifies all evidence hashes and compares the complete JSON outputs of seven experiments to the archived receipts. All finite decisions use the Python standard library. To authenticate the source files as well, add `--source /path/to/original-checkout`. The [original revision](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and the [previous experiment](https://github.com/nousentllc/riemann-hypothesis/tree/b7b5bc6e5e6814f654753fcbd5f45fecf370344c/research/uriel/experiments/zero-and-arithmetic-windows) have different roles.

For both supplemental Lean replays also pass `--toolchain /path/to/lean-4.33.1 --mathlib /path/to/built-mathlib`. Use Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, with its compiled dependencies present. Each replay compiles a module, checks its axiom report and runs `leanchecker`. The ten reported declarations cover scalar estimates and interval geometry. The full original RH development was not rebuilt.

Compile the manuscript with `latexmk -lualatex Exceptional_Bands_and_Prime_Mass.tex`. It compiles as a single file, including all vector figures. To regenerate those separately, install ReportLab 4.4.9 and run `python3 -B evidence/figures/render.py /path/to/figure-output`. The accompanying ZIP exposes the evidence as editable files. The same evidence is embedded in the TeX between the reproducibility-archive markers after the document ends.

Run `shasum -a 256 -c SHA256SUMS` on macOS, or `sha256sum -c SHA256SUMS` on Linux, to verify the package. Primary protocols are stored in the four evidence directories. Files named FOLLOWUP, SUPPLEMENT, EXTREMA_CONTROL, CROSSOVER and SMOOTH_CONTROL identify subsequent checks. Protocols were written locally ahead of their respective new runs and archived on Git after work began.
