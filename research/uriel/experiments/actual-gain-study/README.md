# When the odd-position loss survives

At one served prime, on one orbit and lift, the proof selects the greater of the direct gain with a zero floor and the specialized gain after its price. The same fully charged odd position can accompany either winner. On the eight-cycle at prime 5, the direct gain recovers 47.00833 units with retained set {0,3} and zero with retained set {3,4}. Both comparisons keep all other scalar inputs fixed. [Exact finite results and controls](evidence/experiments/RESULTS.md)

For the original selected family, the normalized final arithmetic gap equals the preceding study's normalized local allowance minus the actual gain recovered by the fallback on the prime interior, up to a vanishing error. For deliberately selected admissible conductor-one witnesses, a simultaneous adjacent-pair condition makes the specialized branch win on all sufficiently long served orbits, uniformly in the lift. This yields actual limiting gap values of √3−3/2, 1/4 and 2−√3. The original unspecified witness's recovery is unknown. These limits are source-based mathematical deductions. [Eight-page manuscript](When_the_Odd_Position_Loss_Survives.pdf) · [Editable LuaLaTeX](When_the_Odd_Position_Loss_Survives.tex) · [Preceding study](https://github.com/nousentllc/riemann-hypothesis/pull/10)

## What to inspect

| Question | Primary material |
|---|---|
| Why does the fallback sometimes erase the apparent loss? | [Identities and first-step decision test](evidence/local/SOURCE.md), [source-linked Lean supplement](evidence/local/ActualGain.lean) |
| What can be evaluated on a fixed orbit and lift? | [Registered primary panel](evidence/experiments/DESIGN.md), [first follow-up](evidence/experiments/FOLLOWUP.md), [stronger rank control](evidence/experiments/RANK_FOLLOWUP.md), [exact output](evidence/experiments/results.json) |
| Where does recovery enter the actual final demand and tax? | [Source-level derivation, both lower bounds and prime aggregation](evidence/transport/TRANSPORT.md) |
| Can the same retained set meet the condition for many different primes? | [Matching experiment design](evidence/MATCHING_DESIGN.md), [exact distributions and correlated ablation](evidence/matching-results.json), manuscript sections 6–7 (pages 7–8) |
| What was kernel-checked? | [Local replay instructions](evidence/local/README.md), [original-interface replay receipt](evidence/local/verification.json), [scalar transport replay receipt](evidence/transport/kernel.json) |
| Which original files support the derivation? | [Authenticated line ranges and hashes](evidence/source_anchors.json) |

The finite rank controls assume the orbit is served and use explicit price and tax coefficients. They do not supply the host, its retained arithmetic witness or the entire family of compatible parameters. The first single-lift panel violates full rank/size premises. The stronger two-lift panel enforces the displayed rank inequalities, with two high-range threshold costs, the DI coefficient and prime-wide ep set to zero. The full weighted prime limit and simultaneous selection argument were derived on paper. The Lean run covers the named local and scalar statements. A full Lean build to an RH endpoint was outside this experiment.

## Reproduce

From this study's directory, Python 3.11 or newer suffices for all numerical tests. They use exact rational arithmetic.

~~~sh
python3 -B evidence/experiments/cycles.py > /tmp/uriel-actual-gain-cycles.json
cmp /tmp/uriel-actual-gain-cycles.json evidence/experiments/results.json
python3 -B evidence/matching.py --check
shasum -a 256 -c SHA256SUMS
~~~

The optional flag on the cycle program emits all 255 raw primary masks while keeping the recorded summary on standard output. The matching check covers 72 distributions using 18,432 weighted mask/orbit evaluations and a dependent-selection negative control.

To authenticate the original source, use a Git checkout containing commit 40e56bab026552e089d7afcfeff08d2defb9c005 and an export of its tree containing the src directory. To compile the manuscript use a LuaLaTeX installation with the packages listed in its preamble.

~~~sh
python3 -B evidence/check_sources.py --repo "$RH_CHECKOUT" --original "$RH_ORIGINAL"
latexmk -lualatex -halt-on-error When_the_Odd_Position_Loss_Survives.tex
~~~

The [local replay guide](evidence/local/README.md) gives the pinned compiler, library and dependency requirements. The [transport guide](evidence/transport/TRANSPORT.md) documents the separate scalar replay. The experiment adds research files under its own directory. The original source pin and branch base are [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and [08188ff](https://github.com/nousentllc/riemann-hypothesis/tree/08188ff0c6dd02dfec0bd65d30765862e9db56b7).
