# Target four and the skew Haar

[Paper](Target_Four_and_the_Skew_Haar.pdf) · [Single editable LuaLaTeX source](Target_Four_and_the_Skew_Haar.tex) · [Release ZIP](Nous_Target_Four_Haar.zip)

Take the regular fiber at four for the rank-three Gaussian identity form at the dyadic place of ℚ(√2). Fix the vector measure by assigning the Gaussian coordinate order B = O + Oi volume one. Under the label change j(s) = is the old target measure assigns j(4 + 8O) mass 1/64. Requiring the readable split with skew unit i and trace-one element 1/2 forces target mass 1/32 on the same ball. Its vector tube has mass 257/8192. Consequently the original lattice mass at four is 257/128, and the source-matched split gives 257/256. The stable tube identities on arbitrarily small balls and continuity justify the point value.

The split sends (is,it) to s/2 + it. In the test rectangle above the scalar inverse image of O under s ↦ s/2 is 2O. Its index in O is four. Each copy of the skew Haar therefore needs a factor two for the split to preserve the matched Gaussian volume. The half change in fiber mass compensates exactly. The conditional probabilities that a vector above the depth-five parent lands in its two children are 257/512 and 255/512 in both conventions.

## Where the target-four mass lies

Section 2 of the revised manuscript measures the whole lattice by the first coordinate attaining the minimum valuation. The three rows contribute **15/8, 1/8 and 1/128**. The last row consists precisely of target-four vectors divisible coordinatewise by 2 and accounts for the entire excess over 2. The section also gives the two-pivot overlap as a local lemma, with the metric slope and the Haar volume factor distinguished.

[Finite primitive certificate](ValuationLedger.lean) · [Kernel receipt](valuation_replay.json) · [Physical residue census](valuation_census.py) · [All 18 raw counts at depths 8, 9 and 10](valuation_counts.json) · [Archived chart derivation](https://github.com/nousentllc/riemann-hypothesis/tree/a4cdffe5be81baa134fc9c82219481e0070fc09c/research/uriel/experiments/target-four-chart-overlap)

The finite certificate checks all 32 residues at primitive uniformizer depth five, the restricted convolutions and the exact scaling arithmetic. The passage to the limiting measure uses a written proof that pairs the two next target digits in each fixed first-unit stratum and applies continuity to compact-open tests. The earlier seven chart modules have their own replay receipt at the linked commit. A full RH build was outside the scope of the revision.

## Evidence and limitations

* [New Lean module](TargetFourHaar.lean) and [kernel receipt](lean_receipt.json). Fresh Lean 4.33.1 elaboration and standalone replay cover the split, the literal skew-ball measures, cofinal point identification and a rescaled regular family on the original named completion. Each of 23 axiom queries returned only propext, Classical.choice and Quot.sound.
* [Frozen protocol](PROTOCOL.md), [integer censuses](finite_results.json) and [fourth-root-of-unity certificate](digit_certificate.json). The latter is a post-run independent check of the two depth-six counts. It uses exact integer convolutions and restores the full multiplicities.
* The conditional skew-target result assumes continuity, integrability and compatibility with the matched source slabs. At the readable pin the integral-place contract requires an integral trace-one element. The coordinate order and the larger cyclotomic order have a trace obstruction. No readable-edition integral place or kernel was instantiated. No complete new build of either RH development was run. The observed value concerns the one original coordinate lattice.
* [Source register](source_map.json) identifies the original definition, inherited arithmetic results and readable-edition contracts, with immutable revisions, line anchors and file hashes. The [prior interface experiment](../upstream-interface-comparison/README.md) and the [original upstream review](Upstream_Update_Review_2026-11-25.md) record the context for selecting this test.

## Reproduction

Run the finite calculations from the extracted directory with Python 3 and its standard library.

```sh
python3 -B replay.py
```

The runner checks the archived numerical calculations and compares the two original depth-six counts. To repeat the section 2 kernel check, run `python3 -B replay.py --valuation-lean --sdk "$LEAN_SDK"` with the pinned Lean SDK. This small certificate imports only Init. To rerun the Lean stage, obtain the Lean 4.33.1 SDK at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, built Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474, and the original and study dependencies. The [square-dilate release](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) contains the sources, import inventories and restoration commands. When rebuilding that release use its verification/replay.py with --work to retain the study objects. The present archive supplies the new module and the receipts. Compiled dependencies for both stages are external.

```sh
python3 -B replay.py --lean --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" \
  --study "$STUDY_OBJECTS" --objects "$ORIGINAL_OBJECTS" --receipt fresh-receipt.json
```

Build the single TeX source three times with LuaLaTeX in a writable directory. The original Nous PNG is embedded in the source. The distributed PDF used TeX Live 2026, SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. SHA256SUMS inside the ZIP covers the distributed payload. The paper discloses human and AI contributions on its abstract page.
