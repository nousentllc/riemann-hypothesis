# A regular chart at four

At the ramified dyadic place let K = ℚ₂(√2), O its integers, and B = O + Oi. Fix the Gaussian source Haar so that B has mass one. In the original coordinates, the first physical vector box is (2 + 8B) × (8B)². Its image is 4 + 32O under the Gram map and i(4 + 32O) in skew coordinates.

| Vector box at four | Original scalar mass | Split-skew mass |
|---|---:|---:|
| Parent, width 8 | 2⁻²⁶ | 2⁻²⁷ |
| Centered child, width 16 | 2⁻³⁶ | 2⁻³⁷ |
| One transverse scalar narrowed by one digit | 2⁻²⁸ | 2⁻²⁹ |
| Pivot centered at 10 modulo 16, other entries centered at zero | 0 | 0 |

In the readable hyperbolic frame, write X for the solved coordinate, p for the pivot and v for the residual coordinate. The center is (X,p,v) = (1,2,0). The trace-one element is the field scalar 1/2. The lower two-by-two block for (X−p/2,v) has determinant one over B. A physical box of width W = 2ᵐ centered at (a,0,0), with m ≥ 3 and a in 2 + 8O, therefore has readable parameter preimage (a+WB) × WB × i(W/2)O when s lies in a² + 4WO, and empty preimage otherwise. Its split mass in the active case is 8·4⁻⁵ᵐ. The integral trace obstruction persists.

## What was checked

* **Original edition, Lean 4.33.1.** The inherited target-Haar comparison and five chart modules were elaborated and replayed. Named results include the original Gram equation, joint inverse, exact physical slab at all qualifying precisions, normalized Borel measure preservation, centered parent and child, missing child, and invertibility of the hyperbolic pivot throughout the parent.
* **Readable edition, Lean 4.35.0.** The literal upstream disintegration module was freshly elaborated and kernel replayed with 27 pinned project imports supplied as compiled objects. The field formula agrees definitionally with its flatChart when given a Place. Its field-only calculation is realized in the original Gaussian identity space using an explicit frame and a Hensel witness. A separate replay verifies algebraic box rotation, real correction, lower inverse and product-weight arithmetic.
* **Written proof.** The paper assembles the exact readable parameter rectangle, including its necessity at an inactive target, and evaluates the prescribed parameter product Haar. The full pointwise set-preimage-to-pushforward argument for that rectangle is written mathematics. The old-side measured endpoints and the readable-side component lemmas have separate formal receipts. A concrete upstream Place with its character and Fourier-kernel bounds remains open, as does gluing charts globally. The full RH project was outside these replays.
* **Independent computation.** The original squared-norm program regenerates 100 integer-count records and partitions all 4,096 original children. A second program pushes 1,024 parameter cells per case through the rational readable formula into all six physical coordinates, checking the target of each vector. Six positive image sets match the independent physical sets exactly; one is empty at four. Halving the skew parameter width produces only 256 distinct children. The follow-up protocol records that this control was designed after the original census.

## Package and sources

The single editable LuaLaTeX file contains the original Nous PNG. The PDF includes the paper, annotated formal evidence and source register. The ZIP includes both documents, executable sources, exact data, three replay receipts and SHA256SUMS. The front matter credits human and AI contributions.

The source pins are [the original edition](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005), [the prior square-scale study](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates), [the previous Haar calculation and upstream review](https://github.com/nousentllc/riemann-hypothesis/tree/4be022986be0e29b4d38f9d04b17956131fe4d56/research/uriel/experiments/target-four-haar) and [the literal readable chart](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/General/Measure/QuadricDisintegration.lean#L239). The included TargetFourHaar.lean is a byte-identical copy of the previous release's module.

## Reproduction

The numerical checks require Python 3 and its standard library. Run them from the extracted directory.

```sh
python3 -B replay.py
```

For the original-side replay, use the compiler and Mathlib pins in original_replay.json. Restore the original compiled imports and study objects using the square-scale study linked above. Its verification/replay.py accepts --work to keep its study objects. Then run

```sh
python3 -B replay.py --lean --sdk "$OLD_SDK" --mathlib "$OLD_MATHLIB" \
  --study "$STUDY_OBJECTS" --objects "$ORIGINAL_OBJECTS" --receipt fresh-original.json
```

For the readable side, use the checkout at e063a923 and its official Lean 4.35.0 SDK. Prepare its published dependencies with lake exe cache get as documented by that edition. The runner checks every reused project object against readable_inputs.json, recompiles the chart from its pinned source and rebuilds the study modules from this package. The algebraic box calculation only uses its Mathlib environment.

```sh
python3 -B replay_readable.py --sdk "$READABLE_SDK" --repo "$READABLE_CHECKOUT" \
  --receipt fresh-readable.json
python3 -B replay_parameters.py --sdk "$READABLE_SDK" \
  --mathlib "$READABLE_CHECKOUT/.lake/packages/mathlib" --receipt fresh-parameters.json
```

All replays check the queried axioms against propext, Classical.choice and Quot.sound. The standalone checker replays the declarations of each named module relative to its compiled imports. The archive does not bundle compiler installations, Mathlib or the upstream cache.

Compile the single TeX source three times with LuaLaTeX. The release used TeX Live 2026, SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. SHA256SUMS covers the uncompressed payload files.
