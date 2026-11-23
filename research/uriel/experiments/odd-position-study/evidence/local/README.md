# Odd-position partner slack

[SOURCE.md](SOURCE.md) defines the signed local excess, derives its exact unused-column series, and gives the two-sided bulk estimate and the source interfaces that limit its propagation. [OddPartnerSlack.lean](OddPartnerSlack.lean) imports the pinned original theorem module. All supplemental declarations live in `Formalism.MainNotions.AuxBlock8.Pf.St.OddAudit`.

## Formal results

| Declaration | Content |
|---|---|
| `clip_formula`, `clip_bounds`, `no_clip`, `full_clip`, `favorable_lift` | Exact signed row at any distance, its three clipping regimes, and the lift threshold |
| `exact_excess`, `unused_nonneg`, `signed_orbit_bound` | Source kink with signed offsets on odd retained rows, including an exact orbit identity |
| `series_partition`, `unused_eq_skipped` | Finite selected distances and the exact complementary infinite odd-exponent series |
| `deep_row`, `boxed_first_row`, `bulk_row` | Zero clipping past distance one in the cubic range, complete clipping at an adjacent row inside the box margin |
| `one_charged_iff`, `first_thin` | The first column is unused precisely at a missing successor, where only the thin-fill allowance applies |
| `skipped_column_bound`, `unused_le_holes_tail` | The geometric bound for the entire unused series, including its first term and all odd exponents from three onward |
| `bulk_sandwich`, `positive_part_squeeze` | Signed two-sided orbit interval and the scalar comparison for its positive part |

## Independent rational controls

[check_bulk.py](check_bulk.py) enumerates every mask on cycles of lengths 2, 4, 6, 8 and 10 at the four primes 101, 251, 5003 and 8009. Three lift values test zero lift, a small positive lift, and a lift above the top offset. The last is an adversarial control for the algebra. It does not claim to arise on a selected large-scale family. The synthetic parameters are \(H=10000, x=10, b'=100, \eta=(b'/x)/200\), and the global rank is set to twice the orbit length. Finite integer levels are chosen inside a model upper margin. The cycle masks are unrestricted, including empty, all-even and all-odd masks. This model tests the local statements independently of a global arithmetic witness.

The script sums exact fractions up to the first odd exponent beyond every used exponent at which the geometric majorant falls below every fill. From that exponent onward all minima equal the majorant, and the infinite remainder is evaluated as a geometric series. Every test compares this direct full sum, the selected-summand formula, the complement, and the two-sided inequality. The 16,368 cases yield 15,382 residuals below the unpaired baseline, 926 above, and 60 equal. Of these, 8,300 signed residuals are negative. Thus exact equality to the unpaired baseline can fail on either side, even with an exact geometric tail. Five separate row controls pass through zero distance, the lower plateau, the interior of the clipping interval, the upper plateau, and a late predecessor. [Numerical results](bulk_results.json)

From this directory the standard-library-only replay is

```sh
python3 -B check_bulk.py > /tmp/odd-partner-bulk.json
cmp /tmp/odd-partner-bulk.json bulk_results.json
```

## Replaying Lean

Use a checkout containing both the research experiment helpers and the original Git object `40e56bab026552e089d7afcfeff08d2defb9c005`. Set `RH_CHECKOUT` to its root. Export its `src` tree at that commit beneath `RH_ORIGINAL`. Set `LEAN_ROOT` to the pinned Lean 4.33.1 installation, `MATHLIB_ROOT` to the matching checked-out and compiled Mathlib tree, and `RETAINED_LIBRARY` to `lib` from a verified retained-host replay. `RETAINED_RECORD` is the JSON receipt for that library. The verifier authenticates the toolchain revision, package manifest, and retained library inventory before reuse. The [retained-host reproduction guide](https://github.com/nousentllc/riemann-hypothesis/blob/e674cb750ef96b2f5e7cd46586ea4edb9998715a/research/uriel/experiments/joint-witness/REPRODUCE.md) describes the original toolchain setup, and the [retained-host build and cache instructions](https://github.com/nousentllc/riemann-hypothesis/blob/93cbbeec3e1542566bf98f6dd66098dfda851ed8/research/uriel/experiments/retained-host/REPRODUCE.md) describe the base library.

```sh
python3 -B replay.py --checkout "$RH_CHECKOUT" --original "$RH_ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB_ROOT" \
  --library "$RETAINED_LIBRARY" --manifest "$RETAINED_RECORD" > /tmp/odd-partner-kernel.json
```

The default builds the four missing original modules from their pinned sources and passes each object through the standalone `leanchecker`. For the recorded run those four sources were compiled in a separate clean directory. The optional `--staged-originals` checks their source bytes and replays their objects. The optional `--original-object-manifest` compares object hashes with the published SHA-256 inventory. The script then compiles the supplement, checks the exact set of 19 axiom statements, and runs `leanchecker -v OddPartnerSlack`. [Verification receipt](verification.json)

The supplement's project import closure has 293 modules. The authenticated base library supplies 289 of them. All four additional original objects differ in SHA-256 from their published counterparts, despite the pinned source and successful kernel replay. The comparison establishes source-level replay on the recorded toolchain and platform. It leaves byte-for-byte object reproduction and an independent full-library build open. `leanchecker` is a separate process from the same Lean distribution. The arithmetic data, prime distribution, limiting family, and RH endpoint are outside the local replay.
