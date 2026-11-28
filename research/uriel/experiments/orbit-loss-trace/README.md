# What the bad-orbit bound buys

A one-point exchange can change the orbit verdict for every retained point on a large orbit. How much of that sensitivity reaches the proof's global loss estimates? At fixed data, the source pays at most four times the rank, scale, and weighted bad-point count for one omission term. A distinct prime estimate continues to contribute at the main scale. A second loss comparison has enough room to absorb the full ordinary orbit allowance under its published ceiling.

[Seven-page report](What_the_Bad_Orbit_Bound_Buys.pdf) · [Editable LuaLaTeX manuscript](What_the_Bad_Orbit_Bound_Buys.tex) · [Pinned declaration trace](evidence/SOURCE_TRACE.md) · [Experiment design](evidence/DESIGN.md)

## Findings

| Estimate | Ordinary allowance | With zero bad mass |
|---|---|---|
| Served-point omission | At most 4maB, where B is the weighted count of bad retained points | Exactly zero |
| Demand minus gain | At most (2 log(4) C + 12g)U + 4maB. The standard cap gives 4maB ≤ 4x^(−1+ε)U | At most (2 log(4) C + 12g)U. Its high-prime budget has a floor of 2 log(4) C U |
| Combined positive prime deficits | The individual allocations sum to 113U/24 | The surviving allocations sum to 281U/60. Both fit under 5U |

Here the scale is U=m|T|b, a=xb and g=100K x^(4ε−1). Under the source assumptions, the weighted bad mass B is bounded by |T|x^(−2+ε). The two rows concerning global gaps describe different inequalities. The 0.53% difference in the prime-deficit calculation is a fraction of its unrounded allocation. There is no measured change of that size in any arithmetic witness.

The source trace follows direct references from the original headline construction to the family loss calculation. The proof ultimately uses a uniform constant and a zero loss exponent at that step. For fixed C>0, deleting bad-orbit costs still leaves a positive leading coefficient in the current high-prime budget. Going back one step, retaining the actual number of served points at each prime changes its normalized log-weight by at most B/|T|. This becomes zero in the all-good case. The outstanding question concerns the log-weight of the served inert primes outside the chosen drop set.

## Reproduction

From the study directory, run the exact finite controls using Python 3.

```sh
python3 -B evidence/check_budgets.py --check evidence/budget_results.json
```

The script exhausts the 81 admissible subset configurations for four labels, the 512 corners of the prime-deficit budget and the 256 corners of its zero-orbit face. Three exact power-of-two scales check how much of the family loss allocation the ordinary orbit cap can occupy. A further 324 comparisons check the served-point weight inequality. Removing the prime cutoff gives an explicit failure. [Recorded output](evidence/budget_results.json)

To verify the source locations, supply a Git checkout containing original commit `40e56bab026552e089d7afcfeff08d2defb9c005` and an unpacked copy of the same original source. A complete checkout of that commit can serve both roles.

```sh
python3 -B evidence/check_sources.py "$CHECKOUT" "$ORIGINAL"
```

The two Lean supplements use Lean 4.33.1, pinned project modules and the original Mathlib package revisions. Each subdirectory documents the required inputs, independent kernel checks, and precisely which cached dependencies were used. [Family loss replay](evidence/discriminant/README.md) · [Prime-deficit replay](evidence/lean/README.md)

To rebuild the manuscript, run `latexmk -lualatex -halt-on-error What_the_Bad_Orbit_Bound_Buys.tex` in a working copy. The source links resolve to the original commit. The study makes conditional statements at two specified consumers, assumes the original size and selection premises, and does not realize an all-good selected family. A full build of the RH entry point was outside this focused replay.

[Preceding weighted-orbit experiment](https://github.com/nousentllc/riemann-hypothesis/pull/7) · [Original source](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)
