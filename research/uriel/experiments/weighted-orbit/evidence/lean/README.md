# Weighted orbit condition in Lean

This supplement imports the pinned definition of `GlobalTheory.EX.BadOK`. The public pinned source is [ThinScalesIffHostBound.lean](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean#L36-L43). The local Good predicate calls [the orbit interval and tile condition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L10-L26).

## What the kernel checks

- `every_arrangement_good` gives a parameter region in which every possible placement passes. Its order must lie below one full tile and below or at both occupancy caps.
- `one_tile_iff` removes the tile look-ahead parameter when exactly one complete tile fits. `good_one_tile_iff` keeps both window conditions while making that one marked tile explicit in the original good-orbit predicate.
- `width_two_marked_iff` checks the evaluator’s exact width-two criterion on every tile of the source. Relative to the tile start, the retained positions inside it must be exactly 2 modulo 4. Positions outside that tile are unconstrained by its individual markedness.
- `tiles_iff_exists` handles multiple complete tiles. When the look-ahead spans at least their number minus one and at least one tile fits, the source’s cyclic every-start requirement holds exactly when at least one complete tile is marked.
- `eligible_update` shows why the same prime weights apply to both retained sets when the rest of their host is held fixed. The original definition of the Frobenius choice remains in the statement.
- `badPoints_by_representative` counts retained points over the bad representatives. A failed orbit containing many retained points contributes that many times.
- `mass_zero_iff` and `badOK_zero_iff` characterize zero weighted mass and a zero cutoff by agreement of the good predicate over all eligible prime–retained point pairs.
- `badOK_singleton_iff` cancels the common positive prime weight from the two sides of the source inequality with a singleton eligible prime. It leaves the factor 4, the cutoff constant, inverse-square scale, density and rank in place.

These are general statements with the indicated premises. In particular, the singleton statement assumes the actual arithmetic prime filter is a singleton. A numerical base-level example needs a separate arithmetic identification to instantiate this as a full `Host` example. This audit introduces no assertion of that identification.

## Replay

Use the original sources at commit `40e56bab026552e089d7afcfeff08d2defb9c005`. The [public retained-host replay instructions](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md) specify the pinned checkout, package revisions and compile flags. Run that experiment first. From the directory holding this supplement, pass the public experiment's stored objects and its verification JSON as follows.

```sh
python3 -B replay_orbit.py --checkout "$CHECKOUT" --original "$ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB" --library "$REPLAY_WORK/lib" \
  --manifest "$REPLAY_JSON"
```

The script compares the original Git blobs and compiled object hashes against the public inventory, authenticates the expected compiler and original package revisions, compiles the new source from scratch in a private scratch directory, checks the printed dependency axioms and separately invokes `leanchecker` on the new module. The recorded result is in `verification.json`. The replay covers the new module, using imported objects under the documented trust boundary, without building the entire RH endpoint.
