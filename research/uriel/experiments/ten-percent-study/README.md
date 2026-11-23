# A hand certificate for ten percent

A pattern on 64 cyclic residue classes guarantees that the direct gain recovers at least **12087/120814 = 10.0046352%** of the odd-position allowance for every labeling in the principal conductor-one setting. The class rates depend on the labeling. Each resulting mask keeps the integer nearest the original target and serves all of its primes, orbits and lifts together. The guarantee concerns the limiting recovery fraction on the source windows. Its strict margin also implies recovery above 10% at sufficiently late scales. The pre-existing witness chosen in Lean has no known numerical recovery fraction. [Manuscript](A_Hand_Certificate_for_Ten_Percent.pdf) · [Editable LuaLaTeX](A_Hand_Certificate_for_Ten_Percent.tex) · [Preceding study](https://github.com/nousentllc/riemann-hypothesis/tree/f667dea291ef2a5b204810ad63611ef6b718b18a/research/uriel/experiments/recovery-frontier)

## The certificate

The least label in each dyadic coset specifies its even child. Traversal in preferred-child order places all labelings into a short list of cases. The construction makes selected prime increments miss both orientations of a retained pair. On such an orbit the source-derived local estimates allow the direct gain to recover the odd charge to leading order. The normalizing denominator uses the same mask.

* The ordinary cases have a uniform rate of 64/27 on 27 classes. Seven rules cover the nonreversing matchings. The reversing matching has 16 normalized coordinate layouts, including a single exceptional layout up to affine symmetry. The verifier checks all 16,384 induced matching and orientation combinations and checks the original tile margins at every relevant node. [Coverage table and proof](evidence/alternative/AUDIT.md) · [Exact arithmetic results](evidence/alternative/results.json)
* In the exceptional layout the positive rates are 411/176 on 22 classes, 3/4 on one class and 19/8 on five classes. Their sum is 64. The gain numerator is at least 12087/44 and the exposure denominator is at most 60407/22. An explicit labeling attains both bounds in the finite profile calculation. The full arithmetic interpretation uses the large-host estimates from the earlier study. [Hand calculation](evidence/hand/AUDIT.md) · [Worked labeling, rates and orbit counts](evidence/worked_example.json)
* A 32-residue comparison found an adverse labeling with a 6/61 ceiling for the tested stationary profiles with rate cap 12/5 and abundant realized edges whenever permitted. On the 64-cycle a contiguous six-gap family has 13,312 distinct candidate supports. One labeling defeats them all by forcing an occupied node with an empty canonical even child. These controls explain why a favorable labeling or a simple interval alone cannot certify uniform recovery. [32-residue controls](evidence/designb/AUDIT.md) · [64-residue arc controls](evidence/quotient/AUDIT.md)

The selector compares the squared count error and prime-weighted bad-orbit mass with their mean under its original Bernoulli law. Fixed-count sampling in the prescribed residue classes keeps the count term negligible. The original mark margins, the short-window cap and the long-window tail estimate make the bad-mass term negligible as well. See the manuscript for the probability transfer and the order of quantifiers. [Original internal score](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173) · [Original marked tile](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26)

## Reproduce and inspect

Run these commands from the study directory with Python 3.11 or newer. The 32-residue comparison additionally uses a C++17 compiler accessible as `c++` or selected through `CXX`. The numerical panels otherwise use the Python standard library.

~~~sh
python3 -B evidence/certificate.py --check
python3 -B evidence/alternative/verify.py --check
python3 -B evidence/hand/verify.py --check
python3 -B evidence/quotient/q64_arcs.py --check
python3 -B evidence/designb/run.py --check
~~~

To print a literal certificate, run `python3 -B evidence/certificate.py`. To choose a labeling, give `--labels` a JSON file containing the 64 distinct residues 0 through 63 in increasing order of their numeric labels. The program emits the selected rates, missing steps, exposure and recovered fraction. Its replay matches the worked example and tests 256 additional fixed-seed labelings. Exhaustive coverage of the induced cases comes from the separate verifier. [Certificate generator](evidence/certificate.py) · [Experiment design](evidence/HYPOTHESES.md)

Five supplementary declarations were replayed with Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. They cover the finite matching table, the reversal condition, exceptional ledger arithmetic and the positive-denominator conversion. Source-level fixed-count selection and the global gain transfer remain written arguments. This experiment did not perform a full build of the original proof or compute a finite arithmetic prime threshold. [Lean statements](evidence/kernel/TenPercent.lean) · [Kernel receipt](evidence/kernel/kernel.json)

Set `RH_LEAN_TOOLCHAIN` to the Lean installation with `bin/lean` and `bin/leanchecker`, and `RH_MATHLIB` to a built checkout of the specified revision. For source authentication set `RH_CHECKOUT` to a Git repository containing published commit `40e56bab026552e089d7afcfeff08d2defb9c005` and `RH_ORIGINAL` to an export or checkout of that commit containing `src/`. The paper uses LuaLaTeX.

~~~sh
python3 -B evidence/kernel/replay.py --toolchain "$RH_LEAN_TOOLCHAIN" --mathlib "$RH_MATHLIB"
python3 -B evidence/check_sources.py --repo "$RH_CHECKOUT" --original "$RH_ORIGINAL"
latexmk -lualatex -halt-on-error A_Hand_Certificate_for_Ten_Percent.tex
~~~
