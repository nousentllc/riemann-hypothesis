# Riemann proof research workspace

This directory contains our reading notes and prospective experiments on Levent Alpöge's Riemann Hypothesis formalization and the community's subsequent verification and simplification work.

Start with [RESEARCH_NOTES.md](RESEARCH_NOTES.md). Exact source and verification provenance is recorded in [PROVENANCE.json](PROVENANCE.json).

## Baselines

- **Published proof:** `40e56bab026552e089d7afcfeff08d2defb9c005` in the upstream Git history. This is the original source release, written for Lean 4.33.1.
- **Community development:** the separately recorded upstream commit at import. This branch has changes after the original release, including source reduction and toolchain updates. Read its own `lean-toolchain` and `lake-manifest.json`.
- **Our research:** notes and experiments under `research/uriel/`, on `research/uriel`. New notes do not alter the original mathematical proof or constitute an independent check of it.

The original source remains reachable through Git history and a dedicated local branch. Do not equate a community checkout or one of our research commits with the original release.

## Initial research sequence

1. Trace the prime-window criterion through the analytic lemmas to the five public theorem statements. Record exact hypotheses and dependencies.
2. Reconstruct the relation between theta-lift multiplicity, arithmetic divisibility, size bounds, and the required prime-sum estimate. Mark each explanatory claim with its original source declaration.
3. Test whether shorter explanations preserve hypotheses, quantifier order, and the reasoning needed to rule out counterexamples. Keep formal evidence and explanatory prose separately identifiable.

Any experiments concerning AI memory, calibration, or governance need their own assumptions and validation. The Riemann result establishes no theorem about those systems.

## Verification status

This import is source preservation and selected source inspection. We have not run the complete Lean build or independently checked the entire exported proof. The [Lean and Mathlib joint statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) and [Andrew Sutherland's verification records](https://math.mit.edu/~drew/grh/) describe external verification of the original submission.

A source checkout, a successful download, and a matching Git commit are not a proof-verification run. Before undertaking verification, use the instructions and dependency pins belonging to the exact baseline selected. Full builds require substantially more resources than reading the source.

## Attribution

The proof was announced by Levent Alpöge, working with Claude, on 20 November 2026. Upstream commit authorship and notices are retained. The upstream README states that the submission was published without a license and is mirrored for verification. This research directory does not assign a new license to the imported proof or its supporting third-party material.

Our reading notes were prepared with Uriel on 22 November 2026.
