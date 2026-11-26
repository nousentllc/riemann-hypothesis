# Riemann proof research workspace

This directory contains our reading notes and prospective experiments on Levent Alpöge's Riemann Hypothesis formalization and the community's subsequent verification and simplification work.

Start with [PROOF_CONTEXT.md](PROOF_CONTEXT.md), which reconstructs selected analytic, arithmetic, cohomological, and covolume arguments at the original source pin. Its companion traces and [SOURCE_TRACE.json](SOURCE_TRACE.json) record the inspected declarations. The earlier [RESEARCH_NOTES.md](RESEARCH_NOTES.md) is retained as an initial, more limited reading. Import provenance is recorded in [PROVENANCE.json](PROVENANCE.json).

## Arithmetic witness architecture papers

The [expanded selected-place paper](experiments/selected-place-transport-expanded/) develops the full source and proof sequence and proves that a full original host at d=9239 has one coset and at most 32 signed slots. The earlier study gives the first cardinal obstruction.

The [selected-place transport experiment](experiments/selected-place-transport/) rules out lossless transport of the fixed readable set at q₀=18480 and d=9239. The native original host has at most 44 signed slots, while the readable set has at least 2¹⁰⁷¹ places.

The [joint critical edition of the two interface papers](experiments/proof-interfaces-critical-edition/) compares the corrected prime observable and the source-matched regular fiber, proves the arbitrary-positive-coefficient corollary at positive exponent slack and includes a [16-edition portfolio audit](experiments/proof-interfaces-critical-edition/PORTFOLIO_AUDIT.md).

The [expanded fixed-integer witness paper](experiments/fixed-datum-host-expanded/) classifies when a readable parameter pair meets the original prime conditions and traces the two original estimates to one retained set. The [preceding architecture paper](experiments/window-remainder-architecture/) gives the centered prime-sum identity. The [first witness edition](experiments/fixed-datum-host/) preserves the initial experiment and its replay.

## Baselines

- **Published proof:** `40e56bab026552e089d7afcfeff08d2defb9c005` in the upstream Git history. This is the original source release, written for Lean 4.33.1.
- **Community development:** the separately recorded upstream commit at import. This branch has changes after the original release, including source reduction and toolchain updates. Read its own `lean-toolchain` and `lake-manifest.json`.
- **Our research:** notes and experiments under `research/uriel/`, on `research/uriel`. New notes do not alter the original mathematical proof or constitute an independent check of it.

The original source remains reachable through Git history and a dedicated local branch. Do not equate a community checkout or one of our research commits with the original release.

## Current research phase

The current task is a deeper mathematical reading of the proof. Proposed applications to AI memory, representation, or governance are deferred until the relevant arguments and assumptions are understood.

The latest notes reconstruct the Mellin-transform and localized-Landau mechanism, the actual arithmetic error bracket and exponent losses, a projection/slope/covolume subargument, and the finite-exception logic behind cohomological windows. They also identify the deeper automorphic and arithmetic-geometric dependencies that remain only traced.

The original source is always read at its pinned commit. A source reading, an algebraic check, a proved conditional implication, and an independently replayed complete proof are recorded as different levels of evidence.

## Verification status

This import is source preservation and selected source inspection. We have not run the complete Lean build or independently checked the entire exported proof. The [Lean and Mathlib joint statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) and [Andrew Sutherland's verification records](https://math.mit.edu/~drew/grh/) describe external verification of the original submission.

A source checkout, a successful download, and a matching Git commit are not a proof-verification run. Before undertaking verification, use the instructions and dependency pins belonging to the exact baseline selected. Full builds require substantially more resources than reading the source.

## Attribution

The proof was announced by Levent Alpöge, working with Claude, on 20 November 2026. Upstream commit authorship and notices are retained. The upstream README states that the submission was published without a license and is mirrored for verification. This research directory does not assign a new license to the imported proof or its supporting third-party material.

Our reading notes were prepared with Uriel on 22 November 2026.
