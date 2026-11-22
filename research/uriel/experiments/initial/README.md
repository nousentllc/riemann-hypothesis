# Initial source-pinned understanding experiments

This suite executes five bounded probes of the original 2026 formalization.
It does not test the truth of RH numerically, build the full formalization, or
instantiate the complete arithmetic constructions.

- [Executed results](results/REPORT.md) and [interpretation](INTERPRETATION.md)
- [Preregistered hypotheses and controls](PREREGISTRATION.md)
- [Pinned declaration/assumption map](results/SOURCE_MAP.md)
- [Machine-readable results](results/numerical.json), [partial graphs](results/source_graph.json),
  [test transcript](results/tests.txt), and [runtime/input hashes](results/run.json)
- Preserved [first run](runs/first/REPORT.md), [second run](runs/second/REPORT.md),
  and [environment failure](environment-failure.txt)

## Reproduce

From a checkout of the experiment branch, with Python 3.12 and Git available:

```sh
python3 -m venv /tmp/uriel-rh-experiments
/tmp/uriel-rh-experiments/bin/python -m pip install -r research/uriel/experiments/initial/requirements.txt
/tmp/uriel-rh-experiments/bin/python research/uriel/experiments/initial/run.py --out /tmp/uriel-rh-results
```

The executed local environment was Python 3.12.9, NumPy 2.2.4, SciPy 1.18.0.
The default output directory is `results`; use `--out` to retain the recorded run.
`python -m unittest -v test_suite` also works from this directory.
The runner uses Git objects at the exact original commit, never the current
working-tree Lean files. A partial clone may need network access to retrieve
those objects; unavailable objects stop the run rather than substitute a new pin.
No Lean toolchain is downloaded and no original Lean files are edited.

The script exits nonzero if any regression test fails. Results contain every
selected arithmetic row, all 900 seeded rows, all tested tail parameters, and
failure/negative-control summaries. The cohomology and numeric-slope sweeps are
deterministic exact-rational computations; their seeds and generators reproduce
the individual cases. JSON emission rejects NaN/Infinity. Very large exponential
absorption is marked explicitly rather than silently underflowing.

## Provenance and evidence separation

Original proof: `40e56bab026552e089d7afcfeff08d2defb9c005`.
Research parent: `08188ff0c6dd02dfec0bd65d30765862e9db56b7`.
These are different trees: the original requires Lean v4.33.1, whereas the
research parent has a migrated v4.36.0 toolchain. The installed toolchain was
v4.30.0-rc2. Source reads and all 55 prior hash checks use the original pin.

Preregistration was committed locally as `9525c5b` before execution. Its published
copy is [1782459](https://github.com/nousentllc/riemann-hypothesis/commit/1782459a0a09a158d3cd7e686207133cacd0e40f).
Publishing through the GitHub connection creates new commit metadata, so local
and published commit IDs differ; their Git tree hashes are compared before the
branch is updated. The first-run local commit is `0efddbb`. This is a local
preregistration audit trail, not an externally timestamped registration before
data collection. First/second-run reports preserve their original local IDs.

- **Independent exploration:** signed exponential transforms, real-valued scale
  budgets, rational interval selection, rational slope witnesses, Euclidean lattices.
- **Source-derived results:** exact statements/steps read at the original pin,
  linked in SOURCE_MAP. A body reference proves only that textually visible call.
- **Kernel-checked proof:** no independent Lean elaboration, axiom audit, or
  kernel replay was performed by this suite. The [external MIT verification
  record](https://math.mit.edu/~drew/grh/) is a separate source of evidence.

The source audit covers 65 selected files and 42 curated body references; its
529 import occurrences include 453 outside this selected corpus. It neither
claims a full dependency closure nor interprets every import as a dependency
of RH. Deeper existence arguments remain beyond this experiment suite.
