# The retained-point and served-support comparison

The actual family loss hypotheses carry one retained set, a set of served points at each relevant prime, and a weighted count of bad retained points. The attached Lean modules keep these objects fixed.

Write `I` for a subset of the supplied primes at or below the upper cutoff `X′`. One may restrict it to the inert class and impose the lower cutoff on the same family. Write `S` for those members of `I` that the source classifies as served. Put `N=|TT|`, `θ(I)=Σ log p`, and `V(S)=Σ |TTp(p)| log p`. The effective prime weight is `V(S)/N`. The additions fit together as follows.

| Lean declaration | Statement under its stated hypotheses |
|---|---|
| `missing_identity` | The difference `N θ(S)−V(S)` equals the sum of `log(p) |TT \\ TTp(p)|` when the served sets are subsets of the retained set. |
| `capped_missing_weight`, `family_weight` | For an upper bound `H≥0` on the positive primes of `S`, the difference lies in `[0,H B]`, where `B` is the source's `badPrimeLogWeightedCount`. The family version obtains containment and coverage from `PrimeClassLossHypotheses`. |
| `family_normalized`, `zero_mass_exact` | With positive `H,N`, the normalized gap is at most `x^(−2+ε)` in the family setting. The undivided weights agree exactly at zero mass. |
| `leading_cost` | For `x>0,N>0`, the local contribution of `C b′/x` summed over the specified support equals `2 C U [V(S)/N]/X′`. Here `U=Nmb`. |
| `split_drop`, `drop_weight_bound`, `family_complete_band` | Partition any finite support into retained and dropped primes. A reciprocal-weight allowance on dropped primes turns into a log-weight allowance by the cutoff; the retained-point gap adds independently. |
| `complete_comparison` | Under the original hypotheses and large-scale windows, `0 ≤ [θ(I)−V(S)/N]/X′ ≤ g/(2x) + (x⁹)⁻¹/(2+4θ) + x^(−2+ε)`. Here `g=100K x^(4ε)/x` and the parameter `θ=x^(−ε)` in the denominator is distinct from the prime log-sum. |
| `target_transfer` | If the normalized total prime weight is within `d` of a target `λ`, and service removes a normalized amount between zero and `r`, the normalized effective weight is in `[λ−d−r, λ+d]`. |

`complete_comparison` obtains one shared nonnegative first-class constant before quantifying over parameters, windows, primes and selected data. It calls the sibling `combined_budget` from the drop module. The window facts imply `X′≤X″`. A prime in `I` cannot receive the high class because that would put it strictly above `X″`. Thus every nonserved prime in `I` falls into the first or second class. The proof pays for those two disjoint classes and the omitted retained points separately. No logarithmic density of inert primes is assumed in this statement. It supplies a uniform implication for `PrimeClassLossHypotheses`. Its specialization to an actual inert-prime count also requires the family link, the concrete definition of the inert band, and any distribution estimate one wants to transfer.

## Replay

`replay.py` uses the Python standard library (Python 3.9+) and GNU-compatible Git. It compiles 36 original project modules in an isolated directory, then compiles `ServedPrimeWeights.lean`, the sibling `../drop_lean/DroppedPrimeCosts.lean`, and `ServedBandTransfer.lean` in that order. It runs the separate Lean checker on the last original module and all three additions and audits the axiom output of each statement. It checks the source Git blob for every original module, the compiler revision, and each package revision in the original Lake manifest. Supply an existing Mathlib build for the pinned compiler and package revisions, the original extracted sources, a Git clone containing the original commit, and a new work directory.

```sh
python3 -B replay.py --repo "$REPO" --original "$ORIGINAL" \
    --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB" --work "$NEW_WORK" \
    > verification-local.json
```

For replay against the 36 original objects from the [earlier discriminant run](https://github.com/nousentllc/riemann-hypothesis/blob/1f15c9441034d5d74949d25a498937653f6779a7/research/uriel/experiments/orbit-loss-trace/evidence/discriminant/verification.json), add `--cache "$PRIOR_WORK/lib" --prior-receipt "$PRIOR_RECEIPT"`. This mode verifies every source and object against the pinned earlier receipt. `verification.json` records the local three-module joint replay. The local study also compiled the original dependency closure and the support module from scratch; `fresh-support-verification.json` records that independent check. The compiled Mathlib package objects and installed Lean compiler serve as inputs to both modes. Neither run rebuilds the RH endpoint.

[Original coverage and bad-count contract](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean#L86-L94) · [Original served-point subset](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/SecondKindBucket.lean#L45-L48) · [Original weighted omission theorem](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L32-L74) · [First- and second-class proofs](../drop_lean/DroppedPrimeCosts.lean)
