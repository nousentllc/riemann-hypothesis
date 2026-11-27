# What changes in the compact Lean proof of Dirichlet GRH?

**First source review · 26 November 2026**

**Read alongside the later spacing study.** The original short-window conditions and the compact packing proof have different hypotheses. At the earlier fixed discriminant, the original rank filter makes the literal comparison impossible even before spacing enters. When the discriminant varies, the later investigation obtains two distinct odd partners on the unchanged retained set under its source hypotheses. Its Lean checks and written good-orbit argument are listed separately. This limits any attempt to transfer the compact uniqueness conclusion to the original selector. A correspondence across the full parameter ranges and a native Lean instantiation of the conditional capacity lemma remain open. [Fixed-discriminant obstruction and compact order replay](https://github.com/nousentllc/riemann-hypothesis/tree/d5cdf95bdb5634d812782c464e799f8f5d0546ee/research/uriel/experiments/frobenius-spacing) · [Original same-set collision](https://github.com/nousentllc/riemann-hypothesis/tree/80555206be28204b1d0a9063f54c8f1e2b5fd70d/research/uriel/experiments/global-frobenius)

The clearest change is in the arithmetic-to-analysis handoff. The compact proof fixes the selected set of infinite places and its density coefficient, then chooses an auxiliary cutoff where the **signed combination** of two prime errors is small. It can therefore use a different estimate to finish the same arithmetic comparison. A second change charges the missing dimensions in that comparison as an additive error. These changes explain why the compact edition is worth reading alongside the original argument and the readable rewrite.

The reviewed release is Luke Sernau’s `lsernau/grh-lean` at `72fead102f663d5c7a407964a13dc0cf9d977207`. Both editions formalize RH and GRH for Dirichlet L-functions following the Alpöge–Claude approach. The original archive in our project is `40e56bab`. Our previous readable replay used upstream `e063a923`. The readable edition shipped alongside the compact proof has 763 identical Lean source files, 39 changed files, and one added file relative to that upstream checkout. The readable references below are to the edition shipped in this release. [Pinned release](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207) · [Exact source comparison](source_audit.json)

## 1. The selected places stay fixed while the auxiliary cutoff moves

Write \(M=N_0\), \(T=D.\mathrm{thick}\), and \(R_M(y)=\mathsf{primeError}(d,M,y)\). Here \(T\) is the finite set of places assigned the main cutoff \(x\), and \(R_M(y)\) is the centered prime-power sum with smoothing weight \(1/\nu-1/y\) and a quadratic twist in its coefficient. The exact arithmetic identity is

\[
\operatorname{rem}(D)=
a\bigl[|T|\,[R_M(x)-R_M(x_1)]
       +|\mathrm{tops}|\,R_1(x_1)\bigr].
\]

The set called `tops` here consists of every place in class 1 modulo \(M\). Its cardinality is the tower degree. Dividing by \(a|T|\) gives

\[
R_M(x)=\frac{\operatorname{rem}(D)}{a|T|}
       +R_M(x_1)-cR_1(x_1),
\qquad
c=\frac{\operatorname{towerDeg}(s)}{|T|}.
\]

The readable route uses the prime number theorem to bound both auxiliary errors in absolute value by \(x^{-2}\) at its allowed second scales. It starts with data at sufficiently large integers and passes to real cutoffs using a floor estimate. The compact route constructs a base datum at each sufficiently large **real** \(x\), then holds \(c\) fixed and chooses \(\log x_1\) using the signed expression in the identity. The two source estimates have different hypotheses and quantifiers even though both yield a one-sided bound for the centered prime error at every sufficiently large main cutoff. [Readable one-sided bound](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean#L92-L155) · [Compact remainder identity](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/ShortAndEnough.lean#L84-L97)

The compact window lemma has the following order of choices, where \(E(v)=R_M(e^v)\) and \(F(v)=R_1(e^v)\).

\[
\text{For all sufficiently large }t,\quad
\forall c\in[0,e^t]\quad
\exists u\in[t,t^2]\quad E(u)-cF(u)\le e^{-t}.
\]

The proof takes \(t=10^6\log x\), so its auxiliary error is at most \(x^{-10^6}\). The initial data have \(\log x_1=x^{\varepsilon/6}\ge t^2\). The move to \(u\in[t,t^2]\) retains the lower bound \(t\) on \(\log x_1\) and preserves its upper bounds. In Lean the update is `{D with logX₁ := u, scale := …}`. The places, tower exponent, selected primes, and congruence and three-term conditions are retained. Quantities defined from \(x_1\), including the nominal weight at places outside \(T\), are evaluated on the updated record. The determinant estimate applies to that record. The auxiliary step yields a point in each late log-scale window. In the original archive, the primary-scale hypothesis controlled a prime sum throughout each of arbitrarily late intervals \([Y,Y^{3/2}]\). [Compact data and existence theorem](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/DataExist.lean#L47-L55) · [Compact record update](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L149-L167) · [Original primary-window criterion](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L11)

### What forces a favorable point?

The Laplace transforms of \(E\) and \(F\) are analytic on a disk centered at 4 of some radius \(R>3\). Differentiation under the integral and Cauchy estimates bound the signed moments against \(v^k e^{-3v}\). The weight peaks at \(v=k/3\). The proof chooses \(k=\lceil t^2/9\rceil\), placing the peak in \([t,t^2]\) for sufficiently large \(t\). The moment estimate is \(k!t/R^k\) for each error, so the moment of their difference is at most \(k!t(1+c)/R^k\). [Moment estimate and window proof](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/OneSidedCriterion.lean#L39-L99)

To see how the tails enter, suppose \(E(v)-cF(v)>e^{-t}\) throughout the window. Outside the window the proof uses growth bounds on \(E,F\) and adds two positive terms to make the integrand nonnegative. Relative to the mass \(e^{-t}k!/3^{k+1}\) of the threshold term, the two added integrals have ratios
\[
e^{8t}(3/R)^{k+1}
\quad\text{and}\quad
e^{3t-t^2}3^{k+1}.
\]
The moment upper bound has ratio at most \(3e^t t(1+e^t)(3/R)^k\). Each ratio tends to zero for fixed \(R>3\). The second ratio decays because \(\log(3)/9<1\). This makes the total integral negative for sufficiently large \(t\), contradicting the constructed nonnegativity. The argument supplies a late-tail existence statement. A numerical cutoff or a particular value of \(u\) would require quantitative constants and data beyond the use of that statement in `New.Main`.

The signed estimate has strictly less pointwise information than two separate absolute estimates. For example, with an error tolerance of \(1/4\), \(E=12\), \(F=5\), and \(c=3\), the signed expression is \(-3\) and passes, while both absolute errors exceed \(1/4\). The local Lean replay verifies the algebraic transfer from the signed estimate and the arithmetic bound to the desired bound on \(R_M(x)\).

## 2. The rank deficit has an explicit cost

Let \(D_0\) be the target row dimension, \(n\) the size of the independent family, and \(h\) its log bound per form. The two editions use rank information at different points in their final comparison. The readable edition uses a nonnegative main term plus the loss to isolate \(n m\operatorname{rem}\), then divides by \(n\ge D_0/2\). The compact edition works at full dimension using the exact identity
\[
n h=D_0 h+(D_0-n)(-h).
\]
It has \(0\le D_0-n\le 4D_0/b^2\) and \(-h\le b^2x^{99}\). Consequently the deficit costs at most \(4D_0x^{99}\), or \(4x^{99}\) per target dimension. The factor \(b^2\) from the crude length bound cancels the \(b^{-2}\) from rank coverage. Improving only one input matters according to their **product**. At the level of this inequality alone equality is possible. With \(D_0=4,n=3,h=-16\), the deficit is 1 and the cost is exactly 16. The local Lean check covers both the general inequality and that exact example. The example supplies no information on whether the arithmetic witness can attain both extremes. [Readable comparison](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean#L130-L156) · [Compact comparison](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L121-L145)

## 3. Density is part of the witness

The selected set appears as a field of the compact `Data`. The quantitative bound \(\operatorname{towerDeg}(s)/\log b\le|T|\) appears separately in the conclusion of `exists_data`. It follows that \(c\le\log b\). The same density bound pays for the normalization by \(|T|\) in the main remainder estimate. The update in `New.Main` carries that bound over to the new record explicitly. A trace that extracts the record and drops the surrounding existential proposition loses a hypothesis used at both ends of the argument. [Data fields](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/AdmissibleData.lean#L19-L45) · [Density bound and witness transfer](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Main.lean#L149-L167)

There is a direct consequence for our earlier place-transport experiment at \(q_0=18480,d=9239\). In that experiment the original signed index set has capacity at most 32. In the compact construction let \(B=\log b\). Its scales give \(B^{100}\le x\le m^2\) and \(m\ge2\), hence \(B\le m\). Its exponent and density give
\[
m^{22}=2^s\le\operatorname{towerDeg}(s)\le|T|B\le |T|m.
\]
Therefore \(|T|\ge m^{21}\ge2^{21}>32\). The local check verifies this implication from the stated premises and the capacity contradiction. The source trace supplies the compact premises. Instantiating the new lemma with the actual compact declarations in Lean would complete the cross-edition replay. A quantitative correspondence between the two selection procedures would need a different invariant from injective enumeration onto the old indices. [Compact tower degree and class count](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/Different.lean#L41-L44) · [Original capacity study](https://github.com/nousentllc/riemann-hypothesis/commit/43141b319692e076cd6f6132534a3bec9f86fa39)

One candidate is the **spacing property carried by the set**, which already has two concrete uses in the compact source. In the small-prime branch of `Data.exists_isFrobPacking`, suppose two prospective partners of the same thick place are obtained using powers \(i\) and \(j\) of the same class \(-p\). Raising these displacements to powers \(j\) and \(i\), respectively, gives the same element in the dyadic quotient because \(ij=ji\). The three-term condition forces the first projected displacement to be the identity, and a parameter bound rules that out in the range at issue. This gives uniqueness of the eligible partner, where one exists. In `not_thick_of_short_arc`, a related argument excludes a third thick place along a short local Galois orbit. That proof also needs a separate argument for the prime 2. These are concrete properties to compare with the old selector's orbit certificates. Whether the original selector supplies those properties with the required ranges is an open comparison in this review. [Frobenius packing](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/DepthPairs.lean#L60-L74) · [Exclusion on a short arc](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/ThickSpacing.lean#L43-L57)

## 4. What source compression measures

| Measure | Readable | Compact |
|---|---:|---:|
| Lean files under `src/` | 803 | 794 |
| Physical source lines including blanks and comments | 477,124 | 112,827 |
| Solution export bytes in Sutherland’s audit | 4,485,867,644 | 5,172,274,528 |
| Full build, same audit machine | 32 min 12 s | 33 min 32 s |
| `lean4lean` export check, same audit machine | 2 h 35 min 5 s | 28 min 39 s |

The repository’s headline counts of about 300,000 and 76,000 are code-line estimates. Our physical count includes every line of the source files. The compact Lean source has about a quarter of the lines while its elaborated export occupies about 15% more bytes. The large reduction in `lean4lean` time is concentrated. Sutherland attributes about 2 h 12 min of the readable run to `New.Variety.tiltTheory`, a definition for which the compact edition has a different construction. Lean’s own export checker had comparable runtimes across the editions. For research that uses formal proofs as input, these numbers support reporting source size, elaborated size, and checker cost independently. For reading, the same theorem statement is a starting point for comparing declaration boundaries, with the readable source providing longer derivations and the compact source exposing different proof choices. [Sutherland’s verification report and logs](https://math.mit.edu/~drew/shortgrh/) · [Sonoda’s independent declaration graph](https://shosonoda.github.io/lean-rh-alpoge/grh-proof.html)

## Verification and reproduction

- **Source audit.** The byte comparison of `src/Statements.lean` across editions passed. The file defines four named propositions. Both entry points prove five theorems, including Mathlib’s `RiemannHypothesis`. `source_audit.py` takes the release checkout and the older readable checkout, in that order. The recorded source trees had clean Git status.
- **Local Lean replay.** Lean 4.35.0 and Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679` were used for the shared statement file and the five new algebra lemmas. The two objects use Mathlib imports and cover the statements and auxiliary checks described above.
- **Independent full verification.** Sutherland reports a successful sandboxed theorem comparison for both editions, with all 794 compact and 803 readable modules kernel-replayed. The five endpoint theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. His report includes a separate readable run terminated for memory and a successful readable run on another machine. The full build and endpoint verdicts in this note come from that external audit. [Independent verification](https://math.mit.edu/~drew/shortgrh/)

To reproduce the local algebra replay, use the pinned toolchain and a Mathlib build at the pinned revision. In a directory with the Mathlib package dependencies on the Lean search path, copy the compact `src/Statements.lean` and `AuditAlgebra.lean`. Add the working directory to `LEAN_PATH`. Compile each with `lean -o MODULE.olean MODULE.lean` and replay each with `leanchecker -v MODULE`. [First replay](lean-replay.txt) · [Reconciliation replay](fresh_replay.txt) · [Byte-matched source inventory](source_audit.json)
