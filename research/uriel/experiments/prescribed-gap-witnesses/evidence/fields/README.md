# Coherent exceptional fields across two arithmetic queries

Four new Lean modules strengthen the original first-bound interface and the field-level portion of the earlier endpoint study. The full physical result is conditional on endpoint screens and original arithmetic premises. The implemented semicontinuity is one-sided on the old range.

- `CoherentFields.lean` defines the original shrinking balls at every integer cutoff, proves their first bounds, finite-label stabilization, and a mixed-cutoff lemma.
- `SynchronizedSlots.lean` carries the same center tuples separately through the even and odd arithmetic estimates.
- `SuccessiveFields.lean` makes odd tables independent of the pair and even tables independent of the outer scale after one pair is fixed. Its `gapVAt` couples the two screen heights and allows a direct certificate for odd slots in a finite set D.
- `PhysicalGap.lean` establishes `gapWinDatum` at physical multiplier one for every primitive character. A sufficiently late canonical PairGood pays the original prime and logarithm costs. The same tables, rank constants, pair, page schedule and ambient exponent work throughout the requested gap. Setting D empty tests every odd slot. An actual BbAt certificate for D discharges its endpoint tests.
- `FieldEndpoints.lean` is an exact vendored copy of the earlier PR #18 source at commit `d79bd956c6fb2b8a3de51b606765be81d24fb1fc`. The original arithmetic archive remains at `40e56bab026552e089d7afcfeff08d2defb9c005`.

From this directory, use Python 3.9 or later for the controls and audit. Supply an original source checkout including its src directory. The Git verification additionally needs a repository containing both original and study commits.

```sh
python3 -B field_controls.py > /tmp/field-controls.json
diff -u results.json /tmp/field-controls.json
python3 -B audit.py --source "$ORIGINAL_CHECKOUT" --git "$FORK_CHECKOUT"
```

The Lean runner requires the Lean 4.33.1 distribution and the built Mathlib checkout at `0df444a360eaa60ab8c11dca51a86af692955474`, with its Lake package library directories intact. Mathlib and the Lean standard library are trusted prebuilt dependencies. Source and output files are staged in a temporary directory. Use `--objects` zero or more times for available original object caches. All 702 original Lean sources have content fingerprints corresponding to the pinned Git tree. Each cached original object is checked against its SHA-256 before use. An absent or mismatched cached object is compiled from the authenticated source. A run on a different platform may rebuild additional original objects. `audit.py --git` separately binds the source hashes and 17 line spans to the original Git tree and the vendored prior adapter to its research commit.

```sh
python3 -B replay.py --source "$ORIGINAL_CHECKOUT" \
  --toolchain "$LEAN_DISTRIBUTION" --mathlib "$MATHLIB_CHECKOUT" \
  --objects "$OPTIONAL_ORIGINAL_OBJECT_DIRECTORY" > /tmp/fields-kernel.json
```

The recorded run elaborated all five supplemental modules and replayed each with `leanchecker -v`. It authenticated and reused 702 original objects. It did not rebuild or replay the original project from scratch. Every printed declaration (twelve new, fifteen earlier) reports propext, Classical.choice and Quot.sound. The synthetic controls use integral centers in Q_p and do not identify the obstruction center of any actual source-selected tuple.
