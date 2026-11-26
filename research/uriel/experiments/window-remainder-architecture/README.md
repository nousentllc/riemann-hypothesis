# From arithmetic windows to a prime remainder

The original arithmetic construction bounds a positive family of character ramps on arbitrarily late intervals. The readable construction bounds a signed quadratic-twist remainder at every sufficiently large real scale. They share a smoothing kernel, the pole factor at a putative zero, and the Dirichlet nonvanishing endpoint. Changing the scale and correcting the principal character identifies their observables. Passing between the hypotheses of their analytic criteria requires additional information.

[Read the paper](From_Arithmetic_Windows_to_a_Prime_Remainder.pdf) · [Editable LuaLaTeX](From_Arithmetic_Windows_to_a_Prime_Remainder.tex) · [Reproduction package](Nous_Window_Remainder_Architecture.zip)

## Mathematical contribution

For every positive modulus q, odd prime d coprime to q and real y > 0, multiply the readable remainder by φ(q). The result is the sum over ψ modulo q of the real original centered ramp of ψ minus that of its quadratic twist, both divided by y, plus the sum of log(p)/(p−1) over the distinct primes dividing q. The main theorem is `Architecture.centered_dictionary_euler`. Its hypotheses are weaker than those of the readable arithmetic construction. The latter uses a special modulus and congruence class.

At q = 1 the correction vanishes. At q = 18480 it is approximately 2.208920688 before dividing by φ(q) = 3840. The full-tail coefficient here is 491552. A finite control at this actual main modulus uses d = 9239 and y = 800003/2. Across 34034 prime powers, both representations yield just the term 565122 log(258721)/206977576163 before centering. The hand-checkable small case at q = 1, d = 7 and y = 4 gives log(3)/6. All three sign-reversal controls failed as intended. The test prime is a congruence-class example without any claim about avoiding twisted zeros. [Exact finite results](controls.json)

The previous comparison derived a general formula using a re-centered auxiliary character function and checked old-side identities at modulus one. Here both literal definitions coexist in one Lean environment, and the principal correction is explicitly evaluated. [Previous interface study](https://github.com/nousentllc/riemann-hypothesis/tree/25a06cea18926d375c63cf45d51693a98d821cae/research/uriel/experiments/upstream-interface-comparison)

## Source editions

- [Original window construction](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L26), [original analytic criterion](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L11).
- [Readable arithmetic estimate and endpoint](https://github.com/leanprover-community/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/OneSidedBound.lean), [twist selection](https://github.com/leanprover-community/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/Zeros/Criterion.lean#L37).
- [Upstream guide at the inspected head](https://github.com/leanprover-community/riemann-hypothesis/blob/a7c4d6a94945f49da752e237a6b1e944ab62677e/GUIDE.md), [change propagating the coefficient](https://github.com/leanprover-community/riemann-hypothesis/commit/f2201365d2d57b1deb4fd330aa0da37213457074). The guide's Git blob is identical at the two readable pins.
- [Declaration index, Git blobs and permalinks](source_trace.json). The current-head entries are source comparisons. The readable replay uses the earlier readable pin.

## Reproduce

Run `python3 controls.py` and compare stdout with `controls.json`. With the ZIP extracted, run `shasum -a 256 -c SHA256SUMS`. The package contains the original Nous PNG inside the single TeX file. Run LuaLaTeX three times in a writable directory. For the release byte-level comparison we used TeX Live 2026, `SOURCE_DATE_EPOCH=1795694400` and `FORCE_SOURCE_DATE=1`.

For Lean, use the original source and a corresponding native project build, plus the readable checkout with its project and Mathlib libraries already built or restored. Use the release toolchains recorded in the receipt. The example below names directories relative to the reader's own checkouts. Each replay writes to a fresh temporary directory.

```sh
python3 replay.py --old-source ../original --old-objects ../original/.lake/build/lib/lean \
  --old-mathlib ../original/.lake/packages/mathlib --old-sdk ../lean-4.33.1 \
  --readable ../readable --new-sdk ../lean-4.35.0 --receipt fresh_receipt.json
```

Select `--mode old`, `new`, or `bridge` for a partial replay. For the cross-edition result alone, `python3 replay.py --mode bridge --old-source ../original --readable ../readable --new-sdk ../lean-4.35.0` uses only the readable build and the two source trees. Supply `--current-source` to verify the current-head source index as well. The script validates pinned declaration-source files, compiler revisions and Mathlib commits. It compares each recompiled source to the run receipt, and exits on compiler or checker failures. Object hashes in the receipt identify the recorded run. Byte-identical objects are not required from a different filesystem layout or machine. [Native and joint replay receipt](replay_receipt.json) · [Finite Euler-factor proof](Euler.lean) · [Cross-edition identity](ObservableBridge.lean)

The native replays use prepared imports. The original definition file, by itself, was also compiled under the readable toolchain. This joint environment contains no claim of equivalence between the complete arithmetic witnesses. No full RH rebuild was performed. The human–AI collaboration disclosure is on the abstract page.
