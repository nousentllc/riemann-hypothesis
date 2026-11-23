# Successive prime pairs

The source predicate `PairGood M eps Y X q d` contains the prime row, auxiliary coprimality, twisted prime-sum estimates and two zero-free boxes. The supplementary file proves when two genuine canonical queries can share all four parts. The sole import is the original `Development.AutomorphicArithmetic.CharacterBoxes.PairGood`; the existence assertions `PairEx` and `VWinAt` are explicit hypotheses of the quantified theorems. Their original construction and consumption are documented in the source map. Their unrestricted upstream proofs are outside this supplement's replay scope.

## Reproduce from this directory

The finite controls use Python 3.11 or later and its standard library. Run without Python's optimization switches because independent arithmetic predicates use assertions.

```sh
python3 -B prime_rows.py > /tmp/pair-results.json
cmp /tmp/pair-results.json results.json
python3 -B audit.py --source "$ORIGINAL" --git "$FORK" > /tmp/pair-audit.json
cmp /tmp/pair-audit.json audit.json
python3 -B replay.py --toolchain "$SDK" --mathlib "$MATHLIB" --source "$ORIGINAL" --work "$NEW_WORK" > /tmp/pair-kernel.json
```

`ORIGINAL` is a checkout or complete source extraction of original Git commit `40e56bab026552e089d7afcfeff08d2defb9c005` (with `src` present). `FORK` is any local Git checkout containing this object. The audit also works without `--git`; it then checks the recorded per-file and span digests. `SDK` must contain Lean 4.33.1 binaries, including `leanchecker`. `MATHLIB` is a built mathlib worktree at `0df444a360eaa60ab8c11dca51a86af692955474` with its dependencies. Use a new empty `NEW_WORK` directory for a cold run. For a warm run one may additionally pass `--objects` naming a prior project library. The script accepts a candidate cached object only if its digest matches the manifest. Elaboration and `leanchecker` replay of the supplementary module run in both modes. Platform-specific object hashes may differ between toolchain distributions.

## Receipts and what they establish

* `PROTOCOL.md`, `FINITE_DESIGN.md` specify the hypotheses, control spacings and target before the experiment.
* `source_map.json` and `audit.json` authenticate nine original sources and 22 exact spans.
* `prime_rows.py` produces and checks a chain of eight Pocklington certificates ending at a 1,400-bit prime. The row `q=3` and this `d` pass at log base 36 and both small increments, and the second-prime bands at 36 and 50 are disjoint. The finite row does not estimate any twisted prime sum or populate a cohomological field. `results.json` stores all certificate integers and separate guard outcomes.
* `imports.json` and `kernel.json` cover 21 authenticated and reused original project dependencies, seven named theorems with their axiom reports, and kernel replay of the supplementary module.
* `cold_kernel.json` is the independent cold run. All 21 original project dependencies were compiled from source and the seven results and kernel replay were repeated. The supplementary object had the same SHA-256 in both runs. The SDK and mathlib object installation were shared. The full original formalization was not rebuilt.
