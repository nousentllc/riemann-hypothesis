# Cyclic-window incidence under the original short-window condition

For a finite subset T of the residue positions 0 through n−1, let W(i) be the original set of residues obtained from i by taking offsets 0 through L−1 modulo n. The supplement proves three results.

1. Every position belongs to min(L,n) different starting windows. For each valid offset d, the unique start is t−d modulo n. Offsets exceeding a full cycle add no new positions.
2. Summing |T ∩ W(i)| over all starting positions gives |T| min(L,n). The proof double-counts the incidences between starting positions and retained positions.
3. If the source short-window cap CondA holds, |T| min(L,n) ≤ nK. This also covers n=0 since the subset premise then forces T to be empty.

The target source is [StatementB.lean, lines 9–13](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/StatementB.lean#L9-L13). The source's [window_card lemma](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartA.lean#L113) gives an upper bound on the size of one window. The incidence proof here counts starting positions instead. The numerical rank-band and scale estimates are separate from these three Lean results.

## Reproduce

Use the checkout, original source archive and pinned Lean and Mathlib installation described by the public [retained-host replay](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). From this directory run:

```sh
python3 -B replay_incidence.py --checkout "$CHECKOUT" --original "$ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB"
```

The runner compares StatementB against its pinned Git blob, verifies the compiler and Mathlib package revisions, compiles StatementB from scratch, independently replays it with leanchecker, then compiles and replays WindowIncidence. The original direct dependency of StatementB is Mathlib. The receipt lists the complete flags, package revisions, source hashes and printed theorem axioms. The full RH entry point falls outside this check.
