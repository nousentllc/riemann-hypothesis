# Riemann Hypothesis proof archive: research entry

**Prepared:** 22 November 2026.  
**Original source pin:** `40e56bab026552e089d7afcfeff08d2defb9c005`.  
**Scope:** Levent Alpöge's announced proof with Claude, covering ordinary RH and the corresponding statements for Dirichlet L-functions. This note records selected source readings and research questions; it does not certify the complete proof or extend its conclusions to other L-functions.

## What we have inspected

We read the four-page announcement, selected original Lean declarations, and an independent reading project's guide and bridges. **We have not independently replayed the full archive or audited its arithmetic core.** Reading a theorem declaration establishes what the source claims; independently checking its complete dependencies is a separate task. The reading project's exposition is useful navigation, with its interpretations distinguished from the original formal source.

The first research baseline should retain the original pin, toolchain, dependency versions, and upstream provenance. Our explanatory notes and experiments should remain distinguishable from that baseline.

## A precise analytic interface

For real `y >= 1`, let

\[
G(y)=\sum_{1\le n\le y}\Lambda(n)\left(\frac yn-1\right)
-y\log y+(1+\gamma)y,
\]

where the von Mangoldt function satisfies `Lambda(p^k) = log(p)` for prime powers and is zero otherwise; `gamma` denotes Euler's constant. The original [CharFamily.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean) defines this through a positive-part ramp, together with twisted sums and families having strictly positive coefficients.

The reading project's [WindowBridge.lean](https://github.com/nasqret/riemann-rev/blob/main/references/archive-bridges/WindowBridge.lean) extracts this sufficient condition:

\[
\forall\theta\in(1/2,1)\;\exists C_\theta\;
\forall Y_0\;\exists Y\ge Y_0\;
\forall y\in[Y,Y^{3/2}]:\quad G(y)\le C_\theta y^\theta.
\tag{W}
\]

Its deduction of Mathlib's `RiemannHypothesis` uses the archive's [zeroFree_of_rpow_window](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean) and reflection. A hypothetical zero with real part `beta > 1/2` permits choosing `1/2 < theta < min(beta, 1)`. Condition (W) gives zero-freeness to the right of `theta`, contradicting the hypothetical zero. Reflection handles the opposite side.

The quantifiers matter. Constants and windows may depend on the exponent. The bound must hold at **every real point of each selected interval**, with intervals available arbitrarily far out. Numerical spot checks do not establish (W). The original analytic theorem accommodates positive character families and fixed widths `[Y, Y^(1+delta)]`, with `delta > 0`.

## The author's proposed arithmetic mechanism

The [announcement](https://alpo.ge/remark.pdf) describes a descendant of Stepanov's finite-field method. Its proposed transfer replaces the role played by high multiplicity with repeated theta lifts between unitary groups. The announced chain length for a von Mangoldt sum of length `X` is approximately **sqrt(X)**; some extracted summaries lose the square-root glyph.

The original [RankVal definition](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean) includes `sqrt(x * delta1) <= m <= 2 * sqrt(x * delta1)`. This is a parameter constraint, not by itself an existence proof for the required arithmetic objects. Divisibility, norms, character averaging, and cohomological losses must all be controlled. The author also warns that portions of the narrative timeline are provisional.

An elementary analogy explains the role of divisibility: if a nonzero integer `A` is divisible by a product of prime powers, then

\[
\sum_p e_p\log p\le\log|A|.
\]

Prescribed divisibility plus a size bound therefore constrains a weighted prime sum. Establishing the appropriate sophisticated analogue is the substantive arithmetic obligation.

## Conditional toy balance

**Illustration, not an independently established estimate from the archive:** suppose an admissible construction had error `E(m) = x/m + m`. The competing terms balance at `m = sqrt(x)`, giving `E(m) = 2 sqrt(x)`. Equivalently, with `m = x^alpha`, the larger exponent is `max(1-alpha, alpha)`, minimized at `alpha = 1/2`.

The [independent architecture guide](https://nasqret.github.io/riemann-rev/guide/proof-guide.pdf) describes the proof's bookkeeping using this balance with additional terms and exponent losses. We have not reconstructed that estimate from its full original dependencies. The optimization explains a parameter choice only after the estimate and admissibility conditions are proved.

## Positivity protects the analytic signal

The original [poleData.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean) constructs a positive weighted sum of zero multiplicities, `S > 0`, and residue `-S/[rho(rho-1)]`. Positive weights prevent cancellation of the common complex factor. For a real zero in `(0,1)` the residue is positive; for general complex zeros it need not be real or positive. Positivity of `S` establishes noncancellation.

## Research questions and next work

1. **Extract the smallest useful obligation.** Reconstruct the dependency path from (W) to RH, recording definitions, assumptions, and the exact quantified conclusion. Determine which analytic lemmas remain useful independently of the arithmetic construction.
2. **Separate mechanisms from naming.** Identify the precise property that each theta lift preserves or strengthens. Check whether explanatory terms such as multiplicity match the actual formal declarations.
3. **Locate simplification opportunities.** Compare three hypotheses: the length chiefly reflects necessary mathematics; it chiefly reflects formal scaffolding; or both contribute substantially. Measure dependency reuse and removable duplication before choosing among them.
4. **Test explanation quality.** For each compressed explanation, preserve a link to the declaration it describes. Ask whether it predicts which assumptions are necessary and which counterexamples they exclude.

For our memory and governance work, these suggest practical experiments in assumption tracking, dependency-preserving compression, and independent verification. They are workflow analogies; they establish no result about QFTN, SymMem, or Entropy Geometry. Any mathematical transfer requires its own definitions and proof obligations.
