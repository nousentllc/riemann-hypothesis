# A zero and the prime windows

This experiment asks what a hypothetical Dirichlet zero with real part greater than one half would force a smoothed prime sum to do. The paper follows the same observable through the analytic and arithmetic arguments in the pinned Lean source, then tests it on manufactured signals and on actual prime powers.

**[Read the 31-page paper](A_Zero_and_the_Prime_Windows.pdf)** · **[Open the single-file LuaLaTeX manuscript](A_Zero_and_the_Prime_Windows.tex)** · **[Reproduction guide](evidence/README.md)** · **[Provenance](PROVENANCE.json)**

## What the experiment found

* **Analytic consequence.** For a hypothetical zero with real part β, choose 1/2 < θ < β and a positive window-width parameter δ. On every sufficiently late window from Y to Y^(1+δ), the positive mass of the smoothed family sum, weighted by y^(−θ−1), exceeds Y^b for each fixed 0 < b < (1+δ)(β−θ). The threshold can depend on b. The [supplemental Lean proof](evidence/analytic/WindowMass.lean) derives the power using a shorter interval at the upper end.
* **Arithmetic comparison.** The pinned construction supplies arbitrarily late whole windows of width δ = 1/2 on which that same family sum is bounded above by y^θ. Its positive mass there is at most (log Y)/2. The [source trace](evidence/arith/arithmetic_sources.json) identifies the construction. The [Lean comparison](evidence/arith/ArithmeticWindow.lean) takes the window supply and matching local estimates as hypotheses.
* **Finite measurement.** On [256, 4096] the square-root-normalized primitive real character sum modulo four has its unique maximum at y = 487. The normalized peak is approximately 0.12991743 and the positive mass is approximately 0.07946046. Across this window the area is 22.05963% of the peak times the logarithmic width. The [primary data](evidence/primes/results.json) cover twelve character, scale and window combinations. A [second integration](evidence/primes/chi4_closed.json) refines the six modulo-four rows.

## Reproduce the work

Unpack the complete ZIP, enter the folder containing this README, and run the following with Python 3.11 or newer. The standard-library runner checks the embedded evidence digests, repeats the numerical calculations and controls, and compares them with the archived results.

```sh
python3 -B evidence/reproduce.py
```

The three primary protocols are in [pole models](evidence/models/PROTOCOL.md), [prime powers](evidence/primes/protocol.json), and [arithmetic witnesses](evidence/arith/protocol.md). Follow-up protocols and their ordering are documented in the evidence guide. Exact endpoints are compared verbatim. Floating-point model diagnostics have the tolerances recorded there.

For the optional formal replay, the [evidence guide](evidence/README.md) identifies the original source, compiled imports, Mathlib revision and Lean 4.33.1 SDK. Pass their four locations to the same runner. The two [analytic](evidence/analytic/window_mass_replay.json) and [arithmetic](evidence/arith/kernel_receipt.json) receipts cover eight supplemental declarations. The full original arithmetic construction and RH endpoint were not rebuilt. Finite data cannot establish the existence of arbitrarily late good windows.

To build the paper, run `latexmk -lualatex A_Zero_and_the_Prime_Windows.tex` with a LuaLaTeX installation. The figures and an independently extractable copy of the evidence are embedded in that one TeX file. To regenerate the vector figures separately, run `python3 evidence/build/figs.py` with ReportLab 4.4.9 installed. It writes three PDFs in `evidence/build/`.

The top-level `SHA256SUMS` covers the paper, manuscript, provenance, guide and expanded evidence. From the package root, use `shasum -a 256 -c SHA256SUMS` on macOS or `sha256sum -c SHA256SUMS` on Linux.
