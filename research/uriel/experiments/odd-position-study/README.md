# Where the odd-position charge is tight

The [local paper](Where_the_Odd_Position_Charge_Is_Tight.pdf) and [editable LuaLaTeX source](Where_the_Odd_Position_Charge_Is_Tight.tex) follow the high inert-prime allowance from [the preceding study](https://github.com/nousentllc/riemann-hypothesis/pull/9). All original-source links are pinned at 40e56bab026552e089d7afcfeff08d2defb9c005.

**Principal conductor one.** Every compatible existing witness has limiting upper local charge at most $1/2-1/(48\exp(1))\simeq0.492335845$. More precisely this bounds a limsup, without requiring the witness's charge to converge. A new selection satisfying the original conditions can attain $\sqrt3-3/2\simeq0.232050808$; another can attain $2-\sqrt3\simeq0.267949192$. These endpoints are sharp for the concentration-around-mean construction using rates between $3\delta/4$ and $\delta$. The supremum over all compatible selections is somewhere between the latter value and the fixed-witness ceiling. The exact value remains open. The local charge is an upper allowance in the global demand-minus-gain inequality, and other gain branches can reduce the actual error.

For a fixed input with distinguished subgroup of index $o$, the same-witness upper bound is $1/2-1/(48\exp(1)o)$. The biased-profile endpoint results above are for $o=1$ only. All limits are at fixed positive admissible epsilon. Neither family thresholds nor the original existential witness are computed in this study.

## Evidence and reproduction

| Component | What is available |
|---|---|
| [Fixed-witness proof](evidence/FAMILY.md) | Uniform prime-step weights on the moving host, adjacency identity, source-based occupancy cap and dyadic rank extremum. The assembled asymptotics are mathematical deductions. |
| [Local trace and replay](evidence/local/README.md) | Nineteen Lean results including the exact signed residual, all unused partner terms and a two-sided bulk bound. Independent rational controls cover 16,368 cases. |
| [Global transfer](evidence/transport/TRANSPORT.md) | A source trace through the per-orbit and per-lift gain comparison. Two Lean declarations check the scalar prime-window criteria. |
| [Alternative selection](evidence/selection/README.md) | Four Lean results for a common retained set, including existence with the original bad-orbit bound under an allowed probability profile. The [selection analysis](evidence/selection/SELECTION.md) traces scope and normalization. |
| [Protocol](evidence/DESIGN.md), [dyadic enumeration](evidence/dyadic_results.json), [prime-step experiment](evidence/prime_step_results.json) | Tests of arbitrary label ordering, exact relaxed extrema and an explicit real-cyclotomic prime computation. |
| [Pinned source manifest](evidence/source_anchors.json) | Original Git blob, SHA-256, citation and line bounds for each linked original file. |

From this directory run the following checks using Python 3.9+ and its standard library. Use the subdirectories' guides for kernel replay with the pinned Lean 4.33.1 compiler and built Mathlib. To check source citations, CHECKOUT contains the pinned Git tree and ORIGINAL contains the extracted src directory.

~~~sh
python3 -B evidence/dyadic.py --check evidence/dyadic_results.json
python3 -B evidence/prime_steps.py --check evidence/prime_step_results.json
python3 -B evidence/local/check_bulk.py | diff - evidence/local/bulk_results.json
python3 -B evidence/transport/check_transport.py | diff - evidence/transport/transport_results.json
python3 -B evidence/selection/finite_selection.py | diff - evidence/selection/finite.json
python3 -B evidence/check_sources.py --repo "$CHECKOUT" --original "$ORIGINAL"
latexmk -lualatex -halt-on-error Where_the_Odd_Position_Charge_Is_Tight.tex
~~~

The 25 audited supplemental statements report propext, Classical.choice and Quot.sound. Four rebuilt original objects in the local module's 293-module closure did not match the earlier compiled hashes. Their pinned source identities and independent kernel replay are recorded. The full RH endpoint and Mathlib were not rebuilt. The source-derived universal constant and optimal profile charges have no end-to-end kernel receipt. The ZIP supplied locally contains the same paper, checks and source files as the new experiment directory. SHA256SUMS covers each released file except itself.
