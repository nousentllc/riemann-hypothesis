# How much of the odd allowance can return?

The original conductor-one selector admits families in which the fallback gain g₀ recovers arbitrarily close to **100% of the local odd-position allowance**. This is a supremum over compatible choices at increasingly large scales. The original proof chooses an admissible mask by existence, and its particular recovery fraction remains unknown. The strongest finite template checked here gives **8.3442%** uniformly over the actual label order, up from the previous **4.4444%**. Percentages use the odd-position allowance as denominator.

The manuscript is [available as a PDF](How_Much_of_the_Odd_Allowance_Can_Return.pdf). Its editable source is [How_Much_of_the_Odd_Allowance_Can_Return.tex](How_Much_of_the_Odd_Allowance_Can_Return.tex). The published proof is pinned at `40e56bab026552e089d7afcfeff08d2defb9c005`. The research branch began from `08188ff0c6dd02dfec0bd65d30765862e9db56b7`. [Original proof tree](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Research context](https://github.com/nousentllc/riemann-hypothesis/blob/08188ff0c6dd02dfec0bd65d30765862e9db56b7/research/uriel/PROOF_CONTEXT.md)

## What the bounds measure

Fix the arithmetic host and its ordering. The selector scores both the total number of retained positions and the prime-weighted mass on orbits that fail its original marked-tile and window tests. For a candidate retained set, the branch comparison holds the prime, orbit, lift and mask fixed. A step that cannot join two retained positions in either orientation lets the fallback recover the odd-position contribution to leading order. The experiments seek many such steps while passing the original internal score. They build new examples to determine what the selector permits. [Selector and score](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173) · [Original orbit tests](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26)

| Experiment | Result and scope | Evidence |
|---|---|---|
| 16 residue classes, rate cap 2.3 | Across all 32,768 orientations, the best uniform guarantee within this restricted class is between 46,000,000/700,425,363 and 23/348. The interval is 6.56744%–6.60920%. One favorable orientation permits 24/115 (20.86957%). | [Design](evidence/search/DESIGN.md), [search and upper certificate](evidence/search/SEARCH.md), [refinement design](evidence/search/REFINEMENT.md), [exact lower certificates](evidence/search/refinement.json) |
| 32 residue classes, one preferred even leaf | The smallest of the best certificates over all 32,768 relevant subtree orientations is 10,367/124,242 (8.34420%). The best orientation gives 19,253/221,426 (8.69500%). All 23 distinct marked-tile parameter checks passed. | [Design](evidence/profiles/DESIGN.md), [selection argument](evidence/profiles/AUDIT.md), [finite outputs](evidence/profiles/results.json) |
| Auxiliary binary groups | At dimension 22 a seeded 512-point support misses 4,065,503 of 4,194,304 differences (96.92914%). Every affine hyperplane contains at least 201 points. A same-size subgroup misses even more differences but has an empty hyperplane. This diagnoses the role of spread in a different finite group. | [Frequency design](evidence/FREQUENCY_DESIGN.md), [measurements and composite-grid controls](evidence/frequency.json) |
| Analytic upper bound and approach to equality | Same-mask gain transport gives an asymptotic upper bound of one. For any fixed tolerance, a sufficiently high-dimensional translated-box construction satisfies the original score and approaches that bound. A quantized variant gives exact rounded size and normalized allowance tending to 1/4. For epsilon = 1/64 and resonance rank 4,096, the first tested power-of-two dimension certifying at least 99% by the sufficient inequalities was 1,048,576. The centers and a finite arithmetic witness at that dimension were never materialized. | [Upper argument and its assumptions](evidence/upper/AUDIT.md), [independent exact-count score audit](evidence/profiles/TORUS_SCORE.md), [grid checks and size bounds](evidence/upper/results.json) |

The small templates constrain rates on whole residue classes. The construction approaching one varies inclusion rates *within* each fixed class. Local windows retain the occupancy the original selector demands, while most differences between positions miss the support. The order of limits matters. Fix the tolerance and the profile first, then let the arithmetic scale grow. The principal deduction uses the previous studies' estimates connecting actual prime steps to group directions, local gain to missing pairs, and dropped mass to a vanishing normalized error.

## What was verified

The finite searches, rational feasibility checks, composite-grid examples, and scalar dimension bounds are executable. The parity-cell geometric-series controls in the upper panel use absolute tolerance `2e-14`. The large-scale existence and prime-weight transfer arguments are mathematical deductions supplied in the accompanying audits. They give no practical first arithmetic scale for 99% recovery. [Finite upper-panel design](evidence/upper/DESIGN.md) · [Torus controls](evidence/upper/TORUS_DESIGN.md)

Lean and `leanchecker` replayed three supplementary declarations. They prove that a missing image difference excludes a retained edge, that local weighted losses aggregate, and that a two-sided gap estimate bounds the recovered fraction for a positive allowance. The recorded axioms are `propext`, `Classical.choice`, and `Quot.sound`. The full torus construction and its arithmetic transfer remain outside these declarations. This study did not execute a full build of the published RH endpoint. [Lean declarations](evidence/kernel/RecoveryFrontier.lean) · [Kernel receipt](evidence/kernel/kernel.json)

## Reproduce the finite experiments

Run from this study's root directory. Use Python 3.11 or later, NumPy for `frequency.py`, and a C++17 compiler accessible as `c++` or named by the `CXX` environment variable. The other numerical scripts use the Python standard library. The binary frequency panel allocates arrays of length 2²².

~~~sh
python3 -B evidence/search/run_search.py --check
python3 -B evidence/search/refine.py --check
python3 -B evidence/profiles/profile_search.py --check
python3 -B evidence/upper/checks.py --check
python3 -B evidence/frequency.py --check
~~~

The search driver compiles the C++ enumerator in a temporary directory and checks its output against [the saved exhaustive record](evidence/search/results.json). The refinement check independently verifies the stored rational witnesses. To repeat its exploratory continuous-rate search, run `python3 -B evidence/search/refine.py` in a disposable copy of the study since it rewrites the saved candidates.

## Replay the kernel, sources and manuscript

Set `RH_LEAN_TOOLCHAIN` to the root of a Lean 4.33.1 installation containing `bin/lean` and `bin/leanchecker`. Set `RH_MATHLIB` to a built Mathlib checkout with its dependency libraries available under `.lake/`. The replay script requires exact Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. It builds the supplementary module in a temporary directory, checks its axiom output, calls the kernel checker and prints a receipt. The saved run used arm64 macOS. [Replay script](evidence/kernel/replay.py) · [Pinned Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)

~~~sh
python3 -B evidence/kernel/replay.py --toolchain "$RH_LEAN_TOOLCHAIN" --mathlib "$RH_MATHLIB"
~~~

For source authentication, set `RH_CHECKOUT` to a Git repository containing the pinned published commit and `RH_ORIGINAL` to that revision's checkout or exported directory containing `src/`. These may name the same directory if it is a checkout of the pinned source. The checker compares original Lean files against their Git blob IDs, verifies cited line ranges, and recomputes the saved anchor manifest. [Source checker](evidence/check_sources.py)

~~~sh
python3 -B evidence/check_sources.py --repo "$RH_CHECKOUT" --original "$RH_ORIGINAL"
~~~

Use a LuaLaTeX installation with Latin Modern Roman and Sans, the LaTeX packages listed in the manuscript preamble, and `latexmk` to rebuild the manuscript from the study directory.

~~~sh
latexmk -lualatex -halt-on-error How_Much_of_the_Odd_Allowance_Can_Return.tex
~~~
