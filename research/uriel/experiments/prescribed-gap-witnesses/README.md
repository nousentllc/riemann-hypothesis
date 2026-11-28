# A prescribed gap and two arithmetic selections

The [35-page whitepaper](A_Prescribed_Gap_and_Two_Arithmetic_Selections.pdf) and [editable LuaLaTeX source](A_Prescribed_Gap_and_Two_Arithmetic_Selections.tex) trace two prospective arithmetic selections back to their prime row, field models, cutoff-dependent exceptional sets and six-part local window datum.

## Answer

For a late interval specified first, one pair of auxiliary primes can serve distinct, sufficiently close outer requests whose ambient ranges contain the interval. Fixed obstruction centers generate coherent lists: on the portion an older query inspected, a later list can only lose exceptions. When the earlier list passes at the left endpoint and the later one at the right, the strict crossover floor(a^Ct) > b^eta lets the later record certify every interior point. At conductor one, the combined theorem produces the original WinDatum with one pair and mark, fixed constants and a fixed page function. The theorem's supplies, thresholds, envelope and endpoint screens all appear in its type. Neither a sparse list nor a cofinal supply of selected windows guarantees those endpoint tests on an arbitrary target.

The fixed odd base at 3 is especially revealing. Its lengths vanish at every positive weight and every layer, so it can be discharged even when its screen fails throughout. A single admissible rank-one center can keep failing on an infinite family of gaps prescribed before all queries. That example does not recover a globally chosen table. An elementary norm-Euclidean proof gives the conductor-one odd roster {3,7}. Lean proves 7 belongs unconditionally and the exact roster conditional on the quadratic class-number-one identity. The remaining obligations are the 2-field attached to the pair and the fixed odd field at 7. A direct, independent finite calculation gives 0.52812895767871 ≤ G(x)/sqrt(x) ≤ 0.64680899314394 for every real x in [8,12]. Neither the finite calculation nor the conditional bridge certifies arbitrary late scalar intervals.

## Experiments

| Unit | Question | Evidence |
| --- | --- | --- |
| [pairs](evidence/pairs/README.md) | When can both actual prime rows be the same? | Seven Lean declarations using PairEx/VWinAt as named hypotheses, disjoint-band controls, and a certified 1,400-bit prime for the finite WinPair example. Its q=3 does not pass the later host construction. |
| [fields](evidence/fields/README.md) | Can field data be fixed before truncations? | Coherent odd tables before either prime, a moving table after the pair, two-endpoint transport, and the original VAt and WinDatum outputs. |
| [stitch](evidence/stitch/PROTOCOL.md) | When can genuinely different screens hand off? | Exact real-interval criterion, simultaneous boundary events, clipped validity domains, and three kernel-replayed supplementary declarations. |
| [slot](evidence/slot/PROTOCOL.md) | How long can an admissible center obstruct a fixed target? | All 729 common refinements versus 177,147 independent pairs, source-scale moduli, cofinal sparse-center proof in the paper, five checked supplementary declarations including the direct zero bound. |
| [roster](evidence/roster/README.md) | Which odd fields remain at conductor one? | Exact prime tests, the written Euclidean argument with margin 11/16, and six Lean declarations. |
| [scalar](evidence/scalar/FOLLOWUP.md) | What does the genuine normalized zeta ramp do on this interval? | A rational enclosure for the continuous extrema, an independent harmonic check and prime-power ablations. The deliberately chosen subinterval ceiling is marked post hoc. |
| [cross](evidence/cross/PROTOCOL.md) | Can an unchanged finite row request an additional ternary digit? | Two outer queries straddle the 52,561st precision boundary. Center 100 persists; another center with the identical earlier record clears the entire active range. |
| [join](evidence/join/PrincipalBridge.lean) | Can the separate results supply one original datum? | One import environment combines the actual prime record, coherent field construction, direct slot proof and roster. The terminal statement exposes the surviving endpoint tests. |

## Reproduce

From the extracted directory, Python 3.11 or later with its standard library is sufficient for all finite controls.

```sh
shasum -a 256 -c SHA256SUMS
python3 -B evidence/reproduce.py
```

For the original source audits, ORIGINAL is the root containing src/. FORK is a local Git repository containing the pinned original, slot-three, class-ascent and PR 18 commits identified in PROVENANCE.json. Those earlier experiments reside on separate research branches. Use normal Git references to fetch any missing commits.

```sh
python3 -B evidence/reproduce.py --audit --source "$ORIGINAL" --git "$FORK"
```

For scoped Lean replay use the Lean 4.33.1 distribution and a built checkout of Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. Optional --objects arguments name cached project library roots. The source auditors check the pins and the runners verify object hashes or rebuild needed inputs as described in each unit. A warm run is much faster than a cold replay. The standalone joint replay also authenticates the 18 prior research modules bundled by content.

```sh
python3 -B evidence/reproduce.py --kernels --source "$ORIGINAL" \
  --toolchain "$LEAN_SDK" --mathlib "$MATHLIB" --objects "$OBJECTS"
python3 -B evidence/reproduce.py --help
```

To compile the paper by itself, copy its single .tex file into an empty directory and run the following command with a LuaLaTeX distribution. Both vector figures are encoded in that file. To regenerate their originals independently, run evidence/figures/render.py with Matplotlib installed.

```sh
latexmk -lualatex -halt-on-error A_Prescribed_Gap_and_Two_Arithmetic_Selections.tex
```

## Provenance and limits

- [Original Lean tree](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005), [research base and proof traces](https://github.com/nousentllc/riemann-hypothesis/tree/08188ff0c6dd02dfec0bd65d30765862e9db56b7/research/uriel), and [the earlier endpoint study](https://github.com/nousentllc/riemann-hypothesis/pull/18).
- [Primary protocol commit](https://github.com/nousentllc/riemann-hypothesis/commit/2ddb0b1a35431324d62739d775c65f1b3f4df46b) and [experiment branch](https://github.com/nousentllc/riemann-hypothesis/tree/experiments/uriel-prescribed-gap-witnesses). Additional mathematical deductions and control thresholds are labeled in the text and evidence.
- [Claim register](CLAIMS.json) distinguishes supplement types, ordinary proofs, exact finite experiments and remaining existential inputs. [Provenance](PROVENANCE.json) records the original and research revisions, verification scopes and document checks.
- The full original Lean development was not rebuilt. The prime experiment cold-built its 21 original dependencies. The broader replays used pinned Mathlib and authenticated compiled prerequisites. The returned prime and center tuples are generally existential. The finite WinPair test does not verify all twist and zero-box conditions for that particular numerical row.
