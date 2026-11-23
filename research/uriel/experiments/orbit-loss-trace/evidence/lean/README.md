# Kernel check of the orbit-loss counterfactual

The module uses the published, finite-set prime-loss comparison in [SecondConstantNonneg.lean](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/SecondConstantNonneg.lean#L86-L109) and the subsequent [low/high estimates](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L29-L174). The original [global comparison](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L189-L254) constructs the bad-count argument from the actual host. The two long proofs adapt the source proof bodies for the low-prime sum and the first clause of the global points lemma. They retain the original rank, host, chosen weight inputs, and all eight component hypotheses.

| Checked statement | Scope |
|---|---|
| `orbitLoss_BTT_zero` | Goodness at the actual orbit representative for every eligible prime and retained point suffices for the original source charge BTT to equal zero. |
| `orbitLoss_E1_difference` | Setting the bad-count argument of the source upper bound E1 to zero removes precisely its seventh summand and leaves the seven others unchanged. |
| `orbitLoss_relative` | The source adm2 hypothesis bounds the scaled orbit term by 3 times x^(-1+epsilon) times the scale U. |
| `orbitLoss_low` | The low-prime upper bound is (559/120)U plus 3ma times the total bad-point charge on the prescribed eligible set. |
| `orbitLoss_global` | Adding the unchanged high-prime bound gives (281/60)U plus 3ma BTT for each finite set of residue-class-zero primes. |
| `orbitLoss_compare` | The first global deficit sum is at most (113/24)U with the ordinary budget; it is at most (281/60)U when BTT=0. |

Here U=m|TT|a/x, m is the source rank parameter, and a in this product is the real scale s.a. The integer functions called a,b in the Lean signatures are the two chosen weight vectors. The pointwise difference concerns an upper bound at fixed inputs. It does not assert the existence of another arithmetic host with zero bad counts or equality for the actual prime deficit. The source’s second global inequality, for the separate ioP quantity, has its own proof.

## Reproduction

Use the published source pin `40e56bab026552e089d7afcfeff08d2defb9c005`. Obtain the helper checkout and local retained-host replay artifacts using [the original replay instructions at 9ac7e1b](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). From the directory containing the supplement execute

```sh
python3 -B replay.py --checkout "$CHECKOUT" --original "$ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB" --library "$REPLAY_WORK/lib" \
  --manifest "$REPLAY_JSON" > verification.local.json
```

The verifier compares the source bytes with the original Git tree, checks the 1,205-module retained-host source/object inventory, authenticates the toolchain and packages, reuses the 282 previously compiled modules in this 289-module closure, and compiles the seven remaining original modules. It kernel-replays each of the seven and compiles and kernel-replays the new supplement. The trusted Mathlib build and previously checked original objects retain the boundaries of the retained-host study. Compiler hashes on another platform may differ. No full build of the RH endpoint is part of this audit.

For a separate compile of the seven original modules, pass its source-and-object directory to `--staged-originals`. This mode checks the staged source bytes and kernel-replays the staged objects before compiling the supplement. The local study used that mode after rebuilding the seven from the pinned source. The optional `--original-object-manifest` records a byte comparison with a published build in addition to the kernel replay.

The recorded comparison used the [published object manifest](https://math.mit.edu/~drew/grh/project-oleans.sha256), SHA-256 `375cbee2fc3fc0f5088ef2e6dc9a5ac5530924310dc62422ec65aac9dc4c1d25`, matching the [earlier independent comparison record](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/second/results/external_objects.json). All seven locally rebuilt original objects had different byte hashes from this manifest. The cause of the differences was not tested for these seven.
