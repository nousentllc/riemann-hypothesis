# Two pivots on one fiber

[Research paper](Two_Pivots_on_One_Fiber.pdf) · [Editable LuaLaTeX](Two_Pivots_on_One_Fiber.tex) · [Complete ZIP](Nous_Target_Four_Chart_Overlap.zip)

Fix the Gaussian identity form of rank three over K = ℚ₂(π), π² = 2. In the six original scalar coordinates its Gram value is the sum of six squares. Let O be the integers of K. Assign O additive Haar mass one, keep the Gaussian vector source fixed, and double scalar base Haar when passing to the split-skew target convention. The inherited experiment measured the full lattice at four under both conventions. This experiment identifies the same vectors and their masses under two coordinate descriptions of a small part of that lattice.

| Physical box around (−6/5, 8/5, 0, 0, 0, 0) | Scalar target image | Scalar density at four | Split-skew density |
|---|---|---:|---:|
| First width 128O, second and four remaining widths 32O | 4 + 512O | 2⁻⁴⁶ | 2⁻⁴⁷ |
| First width 128O, second width 16O, four remaining widths 32O | 4 + 256πO | 2⁻⁴⁵ | 2⁻⁴⁶ |

In the smaller box, solving for the first coordinate gives weight 16 on transverse volume 4⁻²⁵. Solving for the second gives weight 256 on transverse volume 4⁻²⁷. The induced measures agree on **every Borel test**. Using weight 16 in both charts produces a sixteenfold deficit. In the larger box the normalized second pivot is v + v². Its image is exactly πO and each attained value has two distinct preimages. The other five coordinates shift that value by a member of 2O, so they preserve the obstruction. At four the two physical roots with the other coordinates at their centers are ±8/5.

## Evidence

- **Lean 4.33.1.** The seven new modules are elaborated and replayed by the standalone checker relative to their imported objects. For the smaller box the formal results include the joint change of variables, equality of Borel graph measures, actual source slab volumes in both pivot orderings at every refinement, and transverse-restriction tests against the previously released original graph. See [the measure proof](OverlapMeasure.lean), [connection to the previous chart](OverlapEndpoint.lean), and [source-slab proof](TwoSlabs.lean).
- **Wider box.** Lean checks the complete integral image, exactly two roots of the fold, the expanded original Gram expression, the two disjoint inverse balls at positive coefficient depths, the normalized joint tube mass for any spectator probability, and the conversion of numerical weights. The paper identifies normalized coordinates with physical Haar by their affine widths. The direct unreparameterized source-slab replay in both pivots is for the smaller box. See [image proof](FoldImage.lean), [two-sheet measurement](WideSheets.lean) and [full receipt](lean_replay.json).
- **Independent finite checks.** Original physical-square counts, inverse by lifting, and inverse by iteration agree as sets. At normalized depth two each tested small-box target contains 1,048,576 residue vectors. The full six-coordinate wide-box convolution checked all targets at five depths, recording 512 occupied and 512 empty at depth five. The contribution of each occupied target is exactly 2⁵¹ vectors. The finite-quotient cardinality induction for arbitrary depth is a written argument. Files include the [initial protocol](PROTOCOL.md), [fixed follow-up](WIDE_FOLLOWUP.md), [narrow results](results.json) and [wide results](wide_results.json).
- **Scope.** The two new charts both use the original six scalar coordinates. The readable-edition formal comparison uses the separate prior release. These calculations cover a specified local rectangle. The original full development, a global atlas of the Gaussian lattice, and a new instance of the readable-edition place were outside this replay.

## Reproduction

Run from the extracted ZIP. The finite checks use Python 3 and its standard library.

```sh
python3 -B replay.py
```

To replay Lean, use the official Lean 4.33.1 SDK at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and built Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. Restore the compiled original imports and the study modules from the [square-dilate experiment](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates). Its verification/replay.py supports --work to retain the study objects. Obtain the previous study folder at [commit d69e65e6](https://github.com/nousentllc/riemann-hypothesis/tree/d69e65e6ac84b552fd7b0f112570904abe2ebdb1/research/uriel/experiments/target-four-regular-chart). Supply the resulting directories as below. The new seven modules compile in a fresh temporary directory each run.

```sh
python3 -B replay.py --lean --sdk "$OLD_SDK" --mathlib "$OLD_MATHLIB" \
  --study "$STUDY_OBJECTS" --objects "$ORIGINAL_OBJECTS" \
  --previous "$PREVIOUS_STUDY" --receipt fresh-replay.json
```

The default formal command recompiles the three direct parent modules from their pinned sources. The published run used the alternative --prior-objects option with directories of cached parent objects matching the digests in inputs.json. Each release query is checked against propext, Classical.choice and Quot.sound. The archive supplies study sources, results, manifests, and receipts. Toolchains and the previously pinned development are obtained separately.

Compile the single TeX file three times with LuaLaTeX. The source embeds the original Nous PNG and credits human and AI contributions. The release uses TeX Live 2026, SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. SHA256SUMS covers the uncompressed payload. Earlier full-lattice values and their normalization are documented in the [target-Haar study](https://github.com/nousentllc/riemann-hypothesis/tree/4be022986be0e29b4d38f9d04b17956131fe4d56/research/uriel/experiments/target-four-haar).
