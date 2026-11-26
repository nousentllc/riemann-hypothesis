# Target four and the skew Haar

[Paper](Target_Four_and_the_Skew_Haar.pdf) · [Single editable LuaLaTeX source](Target_Four_and_the_Skew_Haar.tex) · [Release ZIP](Nous_Target_Four_Haar.zip)

Take the regular fiber at four for the rank-three Gaussian identity form at the dyadic place of ℚ(√2). Fix the vector measure by assigning the Gaussian coordinate order B = O + Oi volume one. Under the label change j(s) = is the old target measure assigns j(4 + 8O) mass 1/64. Requiring the readable split with skew unit i and trace-one element 1/2 forces target mass 1/32 on the same ball. Its vector tube has mass 257/8192. Consequently the original lattice mass at four is 257/128, and the source-matched split gives 257/256. The stable tube identities on arbitrarily small balls and continuity justify the point value.

The split sends (is,it) to s/2 + it. In the test rectangle above the scalar inverse image of O under s ↦ s/2 is 2O. Its index in O is four. Each copy of the skew Haar therefore needs a factor two for the split to preserve the matched Gaussian volume. The half change in fiber mass compensates exactly. The conditional probabilities that a vector above the depth-five parent lands in its two children are 257/512 and 255/512 in both conventions.

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

The runner checks both calculations against the public JSON files and compares their depth-six counts. To rerun the Lean stage, obtain the Lean 4.33.1 SDK at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, built Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474, and the original and study dependencies. The [square-dilate release](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) contains the sources, import inventories and restoration commands. When rebuilding that release use its verification/replay.py with --work to retain the study objects. The present archive supplies the new module and the receipts. Compiled dependencies for both stages are external.

```sh
python3 -B replay.py --lean --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" \
  --study "$STUDY_OBJECTS" --objects "$ORIGINAL_OBJECTS" --receipt fresh-receipt.json
```

Build the single TeX source three times with LuaLaTeX in a writable directory. The original Nous PNG is embedded in the source. The distributed PDF used TeX Live 2026, SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. SHA256SUMS inside the ZIP covers the distributed payload. The paper discloses human and AI contributions on its abstract page.
