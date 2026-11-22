# Executed initial mechanism suite

Source pin: `40e56bab026552e089d7afcfeff08d2defb9c005`. Research parent: `08188ff0c6dd02dfec0bd65d30765862e9db56b7`.
Preregistration committed as `9525c5b` before suite execution.
Evidence: independent finite exploration and pinned-source inspection; no new kernel proof.

| Experiment | Measured result |
|---|---|
| Analytic residue control | At U=256, positive-residue log(mass/allowance) = 84.5862944; negative-residue mass = 0 |
| High derivatives | 24 quadrature comparisons; max relative discrepancy 3.55e-15 |
| Source tail choice | 9/9 source-constant checks pass |
| Low-sigma ablation | sigma=3 scaled-tail log grows from 4.37942 to 1054.67 |
| Coupled budget | 4/9 selected-scale rows admissible; 4/4 meet the conditional envelope; 900/900 seeded rows meet both |
| Budget identity | 200 independent normalizations; max relative discrepancy 4.83e-16 |
| Arithmetic ablations | 5/5 rejected by constraints; 5/5 exceed the envelope |
| Amplified weak-error control | exact x^10 / (x^5*(x+3)) = 9.99970001e+19 at x=100000 |
| Finite-exception selector | 975 exact-rational whole-interval cases; 0 failures |
| Slope lemma | 500 exact-rational witnesses; 0 failures; 4 single-hypothesis counterexamples |
| Synthetic lattices | 12 projection/lattice cases; denominator-free cut fails in all |
| Source trace | 55 prior hashes checked; 65 pinned source files; 42 curated references; 2 trace failures |
| Regression suite | exit 1; see tests.txt |

Elapsed local runtime (including independent test rerun): 3.658 seconds.

## Interpretation limits

The source tail constants, real-pole sign, coupled rank/density bounds, and denominator
penalty matter in the tested models. Ablated failures are counterexamples to simplified
explanations, not counterexamples to the pinned theorem. The arithmetic grid instantiates
continuous scale inequalities, not actual arithmetic groups, theta lifts, or every source
hypothesis. Exact-rational interval checks test the selector, not cohomology or Sha lengths.
Euclidean lattices do not instantiate the full arithmetic number-field setting.

Full Lean build and kernel replay were **not attempted**: the original pin requires
v4.33.1, the research tree declares v4.36.0, the installed toolchain is recorded in
source_graph.json, and the selected sparse checkout has no dependency/build cache.
The module/import graph and body-reference graph are lexical and partial, not an
elaborated dependency closure or an axiom audit. External verification remains separately
reported at [MIT's verification record](https://math.mit.edu/~drew/grh/), last updated
2026-11-22 16:20 UTC when inspected; this run does not reproduce those checks.

See ../INTERPRETATION.md for the critique, deviations, uncertainty, and next experiments.
