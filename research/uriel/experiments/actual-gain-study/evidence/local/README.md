# Local proof and independent kernel replay

[SOURCE.md](SOURCE.md) derives the mechanism, the four directed successor cases, and a finite test for strict improvement. [ActualGain.lean](ActualGain.lean) imports the original `PartnerCountOfCentral` module and refers directly to the pinned definitions of `gU`, `g0`, `Pr`, `gainP`, `Sv`, `Excl`, `capU`, and `dl`.

| Checked declarations | Scope |
|---|---|
| `source_nonneg`, `demand_split`, `column_partition` | Nonnegative capped and uncapped demands, absolute convergence through geometric domination, exact partition |
| `raw_difference`, `high_charge` | Both occurrences of `dl` cancel in the raw comparison. The high-prime price is the signed offset sum and the exact fixed orbit charge |
| `served_max`, `gainP_split`, `sv_premium`, `served_value` | Actual maximum, sum of all baseline gains plus served supplements, ceiling over the same improvement, and full served gain |
| `excl_one_iff`, `first_directed` | First visit and four directed cases for central nonidentity steps |
| `excluded_deep_zero`, `excluded_eq_first`, `bulk_credit_interval` | Above the cubic threshold the excluded positive-demand sum is concentrated at exponent one. The remaining credit error comes only from even sources |
| `odd_head_interval`, `minima_interval`, `row_tail`, `orbit_tail_budget` | Sharp geometric tail for the available supply, counted once across both branches |
| `premium_stability`, `actual_premium_interval`, `actual_served_interval`, `decision_interval` | Certified first-exponent intervals for the premium, full local gain, and signed branch decision |
| `cutoff_exists`, `demand_zero_after`, `finite_column` | Exact finite reduction of all three column series for supplied witness data |

## Replay

The replay uses Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Start from a checkout containing the research helpers and original commit `40e56bab026552e089d7afcfeff08d2defb9c005`. Export its original `src` tree beneath `RH_ORIGINAL`. The project helpers verify the compiler hash and every tracked package revision before assembling their import path. Build the retained-host library as described in the earlier experiment. [Toolchain and Mathlib setup](https://github.com/nousentllc/riemann-hypothesis/blob/e674cb750ef96b2f5e7cd46586ea4edb9998715a/research/uriel/experiments/joint-witness/REPRODUCE.md) · [Base library build](https://github.com/nousentllc/riemann-hypothesis/blob/93cbbeec3e1542566bf98f6dd66098dfda851ed8/research/uriel/experiments/retained-host/REPRODUCE.md)

From this directory, with `RH_CHECKOUT` set to the research checkout root, run

```sh
python3 -B replay.py --checkout "$RH_CHECKOUT" --original "$RH_ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB_ROOT" \
  --library "$RETAINED_LIBRARY" --manifest "$RETAINED_RECORD" > /tmp/actual-gain-kernel.json
```

`RETAINED_LIBRARY` is the retained-host build's `lib` directory and `RETAINED_RECORD` its JSON receipt. The default verifies project source hashes, authenticates 1,205 retained-library module/source pairs, and builds four missing original objects before replaying them with `leanchecker`. The optional `--staged-originals` reuses the matching separately built sources and objects, checking each source against the original and replaying each object. The optional `--original-object-manifest` adds the published object SHA-256 comparisons. The supplement compiles into a fresh scratch directory. The replay validates all 25 expected axiom statements and invokes `leanchecker -v ActualGain` in a separate process. [Verification record](verification.json)

The imported project closure contains 293 original modules, including 289 supplied by the authenticated library. All four separately compiled original objects passed kernel replay and differed from the published object hashes. The final receipt documents source and dependency authentication, the compiler result, and the standalone checker result from the same toolchain. The finite estimates apply with the hypotheses shown in the Lean declarations. No entire original endpoint build, arithmetic host extraction, or actual-family branch decision was performed as part of this local replay.
