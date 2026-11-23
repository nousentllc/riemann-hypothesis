# Which primes carry the allowance?

This study follows the surviving high-prime offset in the [preceding orbit-loss study](https://github.com/nousentllc/riemann-hypothesis/pull/8). All statements about the original source refer to commit 40e56bab026552e089d7afcfeff08d2defb9c005. The [paper](Which_Primes_Carry_the_Allowance.pdf) and [editable LuaLaTeX](Which_Primes_Carry_the_Allowance.tex) contain both derivations and the coefficient comparison.

## Findings

For each fixed $0<\varepsilon<1/52$ and sufficiently late scale on the chosen family, write $H=\exp(x^{\varepsilon/3})$ and $N=|T|$. Let $I$ be the primes in the high inert band, $S$ the members that the family serves, and $T_p$ its served labels. The effective weight is $\Theta_{\rm eff}=\sum_{p\in S}|T_p|\log(p)/N$. The same host supplies both the conductor bounds and the zero-free boxes. The [arithmetic trace](evidence/CLASS_TRACE.md) derives $\Theta_I/H\to1/4$ uniformly over the eligible indices. The [drop trace](evidence/DROP_TRACE.md) and [family comparison](evidence/lean/README.md) show the effective weight has the same limit. The [secant supplement](evidence/secants/README.md) supports the alternative derivation from three smooth measurements.

For the actual local gain constant $C_G=4|C_\ell|+1$, the leading allowance per unit $U=mNb$ from this offset tends to $C_G/2$. Its all-prime majorant has coefficient $2\log(4)C_G$. The earlier, more detailed per-lift gain hypothesis pays the offset with coefficient one. On that route the leading allowance tends to $1/2$. Section 6 of the paper derives finite bounds for the actual demand-minus-gain gap. Its separate incidence estimate has its own budget. An explicit numerical family, scale threshold and pointwise cohomological exception decision remain unavailable from this experiment.

The computational controls found opposite outcomes at every prime in the eight-prime interval. At one million their inert-prime log-weights divided by the cutoff were 0.2499506569 and 0.2480312498. The smoothed computation includes prime powers and has different numerical values. These controls concern two explicit character pairs. They do not instantiate all the selected-family conditions.

## Evidence and verification

| Evidence | What it establishes |
|---|---|
| [Experiment design](evidence/DESIGN.md), [measured outputs](evidence/results.json) and [finite geometry controls](evidence/drop_geometry.json) | Exact finite signs, counts, symbolic identities and rational inequalities, plus floating-point log sums. The design was written locally before the first numerical run. The failed initial search cap and its extension are recorded. Package and results share one publication commit. |
| [Character checks](evidence/class_lean/README.md) | Six new audited Lean declarations cover the three exact primitive representatives, boxes, uniform unsmoothed estimate, its envelope and limit. |
| [Service and budget checks](evidence/lean/README.md) and [dropped-prime checks](evidence/drop_lean/README.md) | Fifteen distinct audited declarations in the joint replay, including four dropped-prime results. A separate run rebuilt all 36 original dependencies of the service support. |
| [Finite secant checks](evidence/secants/README.md) | Five audited declarations include strict and inclusive secant bounds and the exact triangular width identity. |
| Paper, linked original source and [source manifest](evidence/source_anchors.json) | The combination into the uniform quarter-limit, its use in the gap inequality, and the unit-coefficient refinement are written deductions. The full RH endpoint and Mathlib were outside these replay runs. |

The 26 audited supplement statements reported here exclude helper lemmas and duplicate replays. Each reported axiom list contains only propext, Classical.choice and Quot.sound. The character compilation used authenticated original objects from the retained-host experiment, and the checkers used the pinned compiler and built Mathlib packages. See the module-specific receipts for exactly which original roots were separately replayed.

## Reproduce

From the directory containing this README, the finite runs use Python 3.9+ with the standard library.

~~~sh
python3 -B evidence/probe.py --check evidence/results.json
python3 -B evidence/check_drop_geometry.py --check evidence/drop_geometry.json
python3 -B evidence/check_sources.py --repo "$CHECKOUT" --original "$ORIGINAL"
latexmk -lualatex -halt-on-error Which_Primes_Carry_the_Allowance.tex
~~~

For the source check, CHECKOUT contains the pinned commit and ORIGINAL contains its extracted src directory. For a Lean replay use the instructions in the three linked evidence groups. The [retained-host guide](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md) specifies how to prepare the original archive, helper checkout and toolchain. SHA256SUMS covers the released files. Rebuilding the paper can change PDF timestamps.

## Where the improved coefficient enters the original proof

1. The finite prime set covers prime arguments through the cutoff that clear its inert-in-K condition. The double-negative class implies that condition. The actual served set is the complement of the drop set inside this band. [Prime set and ledger definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/SuppSat.lean#L26-L70)
2. The primitive local formula on the high inert branch has a single copy of the offset. In the termwise majorant the comparison of this copy consumes exactly the nonnegative slack $(C_G-1)b'/x$. All other contributions have independent bounds. [High inert formula](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L581-L585) · [Termwise comparison](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L139-L205)
3. The original local gain inequality permits replacing its cost by any dominating expression. On the band take the mixed expression $\mathrm{loG}-(C_G-1)b'/x$ and elsewhere keep the original envelope. The proofs identify the very same tops by an injective map and the very same gains at the place. The left side subtracts the loss, which fixes the direction of comparison. The family chooses one constant and one remainder schedule before its scale and index. [Gain comparison](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L761-L807) · [Family quantifiers](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L867-L879) · [Transport into the numeric ledger](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L766-L815)
4. The all-prime sum and uniform retained cardinality enter downstream. Keeping the true support of the high-band term preserves its charge exactly. The four residuals are nonnegative, independent of the prime, and jointly bounded after multiplication by the cutoff. The nine other ordinary terms and omitted-point contribution stay under their source bounds. [Prime and cardinality enlargement](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L837-L915) · [Four residuals](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L444-L524) · [Global budget and separate incidence comparison](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L162-L226)
