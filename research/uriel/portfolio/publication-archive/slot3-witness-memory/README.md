# How much of a named witness must a memory record retain?

For one known yes/no question, a single protected bit suffices. For a record that must answer any of 64 later questions, the exact minimum is 65 distinct tag values, or seven bits of fixed-length payload. Both claims have matching encoders and lower bounds. They apply to the family of explicitly designated witnesses in the conductor-one slot-3 experiment. A separate provenance check must bind the tag to the intended witness.

The design question comes from the Uriel-GEMA audit. Its proposed evaluation includes provenance substitution, unsupported answers and coverage, but does not specify a ground-truth task with an exact information requirement. The Nous recovery study supplies a criterion for such a task. An answer is recoverable precisely when all histories compatible with the retained observation agree on it. Here each possible named witness plays the role of a history. This supplies a bounded benchmark and its exact answer key. The existing frozen study has its own prospective model protocol. This follow-up uses none of its model calls or outcomes. [GEMA audit, lines 405–412](../../Uriel_GEMA_Formal_Architecture_Audit.md) · [Nous fiber criterion and coloring bound, §3 and §5](../../nous_provenance_study/validation/part_I_text.txt) · [Frozen study scope](../../nous_provenance_study/governance/DECISION.md)

## Field, observations and target

At cutoff 64 a witness with integral center residue $s$ modulo 81 marks exactly those weights $e$ from 1 to 64 with the same residue as the center modulo 81. The 17 other residues mark nothing. The previous slot-3 result supplies valid arithmetic witnesses for each singleton and the empty outcome. At that commit its formal deduction had an all-layer class-number assumption, supplied mathematically by Yokoi. The [subsequent Lean proof](../../riemann-experiments/research/uriel/experiments/ascent-witness/TowerResult.lean) proves the premise for every layer of these same fields. The published proof itself selects a witness by existence. This benchmark assigns an explicit witness and then deliberately forgets some of its identifying data. The truth queried here is membership for the assigned witness. [Weight table at the pinned commit](https://github.com/nousentllc/riemann-hypothesis/blob/4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87/research/uriel/experiments/slot-three/results/weights.json) · [Checked arithmetic witness family](https://github.com/nousentllc/riemann-hypothesis/blob/4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87/research/uriel/experiments/slot-three/RankZero.lean#L104-L121) · [Choice trace](https://github.com/nousentllc/riemann-hypothesis/blob/4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87/research/uriel/experiments/slot-three/CENTERS.md)

The observation is the witness residue modulo $3^k$ for $k=0,1,2,3,4$, plus the common field, cap, presentation and cutoff. Zero digits gives the same observation for all 81 designated histories. The decoder must answer *undetermined* whenever two compatible histories yield different answers. The executable reference implementation groups histories by the visible observation. An independent decoder counts congruent residues using only the observation and queried weight. All counts below give each of the 81 residues and 64 weights equal weight. They assign no probability to the selection made in the published proof.

## Exact payload size

- **Query fixed before storage.** For the single question about weight 1, store whether the named witness marks 1. Zero bits gives the two witnesses with centers 1 and 2 the same observation despite their opposite answers. One bit is both necessary and sufficient.
- **Any one of 64 queries may arrive later.** The possible answer profiles are the empty set and 64 different singletons. Each of the 2,080 pairs of distinct profiles disagrees on some allowed query. Thus each requires its own tag value. Code the empty set as 0 and singleton {$e$} as $e$. Values 0 through 64 are sufficient. Every six-bit code has a collision because it has only 64 values. In the tested six-bit truncation, the empty set and singleton {64} collide at zero and disagree on 64.
- **Binding is a separate requirement.** Both centers 1 and 2 have a one-element exceptional set. Reusing the second witness's otherwise valid tag reverses the answer for weight 1. A trusted association between tag and witness is part of the channel assumptions. The bit counts exclude the cost of establishing this association, the public lookup rule and any witness authentication. They concern zero-error deterministic decoding with no auxiliary identifying channel.

## Abstention, coverage and missed positives

The table has 5,184 decisions per row. Of those, 64 are positive and 5,120 are negative. Coverage is the proportion of all decisions answered. Positive recall and negative specificity count an abstention as a missed answer of its true class, so their denominators stay fixed. The independent decoders agree on every decision. Every definite answer from the oracle matches the designated witness.

| Observed digits | Certified yes / 64 | Certified no / 5,120 | Undetermined / 5,184 | Coverage | Positive recall | Negative specificity |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 5,184 | 0% | 0% | 0% |
| 1 | 0 | 3,456 | 1,728 | 66.67% | 0% | 67.5% |
| 2 | 0 | 4,608 | 576 | 88.89% | 0% | 90% |
| 3 | 0 | 4,992 | 192 | 96.30% | 0% | 97.5% |
| 4 | 64 | 5,120 | 0 | 100% | 100% | 100% |

Having three digits licenses almost all negative answers and no positive answers. A rule that always answers “no” scores 5,120/5,184 = 98.77% accuracy, while missing all 64 positives. A support-aware controller should report coverage and recall by true label. Selection accuracy alone would hide this failure. The sound oracle has perfect accuracy on its admitted answers wherever it admits at least one. With zero digits it admits none and its selective accuracy is undefined. [All denominators and confusion counts](results.json)

## Falsification controls

1. Swapping the designated witnesses for all 2,016 pairs of distinct positive centers preserves the visible set size but reverses both distinguishing answers for every pair. Keeping only the actual set size licenses 1,088 negatives from the 17 empty-set residues. On all singleton-size observations the selected member remains unidentified.
2. Renaming every history and observation label and reversing input order preserved all 25,920 answers across the five levels. Deliberately assigning the labels for center 1 to center 2 and vice versa was rejected by the independent arithmetic decoder.
3. Replacing the strict proximity test by its weak version at center 1 would additionally mark 28 and 55. Weight 28 is precisely on the boundary. The corruption test rejected this substitution.
4. At held-out cutoffs 26, 27, 28, 80, 81 and 82, crossing a power of 3 changes the strict modulus. Independent valuation labels and the observation-only decoder agreed in all 295,137 decisions across the retained-digit levels. Each cutoff $Z$ produced exactly $Z+1$ answer profiles and the full modulus resolved every query. These are further checks of the arithmetic test implementation.

## Reproduce

Use standard-library Python and a checkout of the fork with the pinned Git object available. Run the following from this directory. The default checkout is the adjacent project mirror under `../../riemann-experiments`. Pass `--repo /path/to/checkout` to the benchmark to use a different clone. The test suite uses the default checkout.

```sh
shasum -a 256 -c PROTOCOL.sha256
python3 -B -m unittest -v test_benchmark
python3 -B benchmark.py > /tmp/slot3-witness-memory-reproduced.json
cmp /tmp/slot3-witness-memory-reproduced.json results.json
```

The benchmark verifies the exact Git blob and the registered protocol digest. All five tests passed under Python 3.9.6 and 3.13.2. Both versions reproduced result SHA-256 `e75608020dbcca576a357554c06d0b62f20273e3fba9b6cfd05233237023debf`. The protocol discloses which counts came from exploratory inspection before registration and which controls were first executed afterward. [Design record](PROTOCOL.md) · [Runner](benchmark.py) · [Tests](test_benchmark.py)

This resolves the minimum tag size and admissible answer coverage for a small, explicitly defined question family. Performance of GEMA or SymMem, robustness to malicious metadata, and generalization to other memory tasks require separate evidence.

A subsequent equal-budget experiment recovered 11 of 64 true positives while increasing total licensed answers from 4,992 to 4,993. It also establishes the optimum at that coverage and records which individual answers change. [Tag-allocation follow-up](allocation/README.md)
