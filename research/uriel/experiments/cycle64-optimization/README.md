# Optimizing recovery on the 64-cycle

For a stationary profile on 64 residues, the best share of odd-position allowance that can be guaranteed over every numerical labeling and every allowed source exponent is **10.11902517624%**, rounded. This result uses the literal marked-tile window certificate for score compatibility and the same fixed-count, edge-realizing host construction throughout. The earlier guarantee was 10.004635224%. The new lower and upper bounds meet in one mathematical expression. The decimal enclosure measures the precision of evaluating that expression.

Read [the paper](Optimizing_Recovery_on_the_64_Cycle.pdf). The [standalone LuaLaTeX manuscript](Optimizing_Recovery_on_the_64_Cycle.tex) contains the complete text and all three vector figures. Copy this one file into any directory and build it with `latexmk -lualatex -halt-on-error Optimizing_Recovery_on_the_64_Cycle.tex` using a normal LuaLaTeX installation with Latin Modern.

## The short calculation

Let C be the larger root of 10 exp(−C) √(C/2) = 1. Let B be the smaller root of B = 0.32 exp((B + 5C)/16). On the exceptional decision of the previous support policy use 26 rates C, a singleton rate B, and an adjustment 64 − 26C − B. For strict rational interior rates, see [the scalar certificate](evidence/marked/limit_corner.json). The sharp fraction is 116C / (2112 + 254C + 32B). Moving the singleton mass affects which cells can supply an even mark. Removing the singleton entirely also changes which cyclic differences exist.

| Experiment | Outcome |
|---|---|
| Original three rate groups, standardized mark | Worst-label supremum 10.04085618% |
| Independent leaf rates, standardized mark | Worst-label supremum 10.11898958% even with free supports |
| Literal trial-count prefactor, rates uniform across exponents | Sharp worst-label share 10.11902517624% |
| Epsilon fixed in advance | Parameter-dependent optimum, e.g. 10.1190959370% at 1/64 |
| Changed support and rational rate menu | 11% on 15,318 of 16,384 normalized sparse charts, for all dense completions of each |
| Complete adverse-label census | Exactly two surviving 28-leaf supports at trial 10.118%, including fixed-support closures |
| Extra loss on the first surviving support | Its upper formula adds 8C to the second support’s denominator |

The label word is 2549776587809433532. At stride s and residue r, bit s−1+r selects which of the two children contains the minimum numerical label. The exact two supports are the bit masks 1230983613671479063 and 1518083709116552983. The census uses two caps, 2.39210 and 2.39213. The larger also covers the fixed-exponent version. There are 3,263,443 legal masks per half. The separate root-hole search visits 42,384 support–step pairs, or 39,058 distinct supports. All are below the trial threshold. Of the remaining sector only the two named masks survive. Their rate inequalities and the rule's lower certificate meet.

## Reproduction

Use Python 3.10 or later and a C++17 compiler. Apple Clang and CPython were used for the release. The verification scripts use the standard library. Run from this directory:

```sh
python3 -B evidence/rates/verify.py --check
python3 -B evidence/lower/check.py --check
python3 -B evidence/geometry/check.py --check
python3 -B evidence/upper/run.py --check
python3 -B evidence/marked/multipliers.py
python3 -B evidence/marked/fixed_label.py
python3 -B evidence/marked/limit_corner.py
python3 -B evidence/marked/exponent.py
python3 -B evidence/rootmark/verify.py
python3 -B evidence/rootmark/independent.py
python3 -B evidence/rootmark/near.py
python3 -B evidence/endgame/project.py
```

The [near-threshold receipt](evidence/rootmark/near.json) gives the signed margins at both caps. [The two residual supports](evidence/endgame/projection.json) record exact rationals for the local projection. For a faster entry point, run the last command and then the full near-threshold check. The last command verifies the stored census and derives its implications. The preceding command recomputes the census. Optional discovery uses SciPy for proposals. Rebuilding the figures with `python3 evidence/figures.py` uses Matplotlib and exports the three figures as separate PDFs if needed. The manuscript embeds the vector originals.

For the fresh finite Lean replay use the matching Lean 4.33.1 toolchain and a built Mathlib checkout at commit `0df444a360eaa60ab8c11dca51a86af692955474`:

```sh
python3 -B evidence/kernel/replay.py --toolchain "$TOOLCHAIN" --mathlib "$MATHLIB"
python3 -B evidence/check_sources.py --repo "$REPO" --original "$ORIGINAL"
```

Here REPO contains the Git objects for the pinned original and ORIGINAL is an extracted copy with its src directory. The source checker authenticates the original file bytes against the Git tree before checking cited line ranges. The local package manifest lists the SHA-256 digest of each delivered file.

## Evidence and interpretation

The design notes in [rates](evidence/rates/DESIGN.md), [lower](evidence/lower/DESIGN.md), [upper](evidence/upper/DESIGN.md), [geometry](evidence/geometry/DESIGN.md), [marked](evidence/marked/DESIGN.md), and [rootmark](evidence/rootmark/DESIGN.md) record comparison classes, proposed tests, and controls. They were assembled during the work and published together on the experiment branch. The new adverse word, two-support collapse and fixed-exponent formula emerged during the investigation. Their checks can be rerun independently of discovery.

The [source notes](evidence/SOURCE_NOTES.md) and [source anchors](evidence/source_anchors.json) identify where the original construction chooses the retained witness, marks tiles, fixes scales, and compares gains. Equation (W) retains the original trial-count prefactor and uses the sufficient failure bound (1−q)^m ≤ exp(−mq). The exact Bernoulli failure exponent or a different selection argument defines a wider possible class. The [kernel receipt](evidence/kernel/kernel.json) records a fresh replay of two finite declarations using Lean 4.33.1. The complete finite enumeration and the transport from profile to arithmetic family are not Lean endpoints in this experiment. We did not rebuild the full pinned RH development for this study. The actual retained set chosen by the proof remains existential. A general score-passing mask can have correlations or use a different argument for passing the score; the sharp upper comparison in this study is specific to the stated certificate class.

[Original pinned source](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Research baseline](https://github.com/nousentllc/riemann-hypothesis/tree/08188ff0c6dd02dfec0bd65d30765862e9db56b7/research/uriel) · [Previous 64-cycle result](https://github.com/nousentllc/riemann-hypothesis/pull/14)
