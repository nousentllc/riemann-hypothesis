# Riemann proof: a deeper reconstruction of selected arguments

**Date:** 22 November 2026.  
**Source baseline:** original published commit 40e56bab026552e089d7afcfeff08d2defb9c005.  
**Status:** selected proof bodies and their interfaces reconstructed from source; no independent full Lean build or kernel replay performed in this workspace.

This document supersedes the immediate research agenda in our first RESEARCH_NOTES.md. The present task is to understand the mathematics and the dependencies well enough to explain why the estimates hold. Proposed applications to AI memory, representation, or governance are deferred. The earlier toy balance x/m + m remains an illustration, not an account of the complete argument.

The companion traces provide declaration names and original source locations:

- [Analytic trace](traces/ANALYTIC.md)
- [Arithmetic and error-budget trace](traces/ARITHMETIC.md)
- [Projection, slope, and covolume trace](traces/COVOLUME.md)
- [Statement semantics and external verification](traces/VERIFICATION.md)
- [Selected immutable source records](SOURCE_TRACE.json)
- [Reproducible elementary budget calculations](checks/reproduce_budget_algebra.py)

## 1. The logical spine is narrower than the archive

The five exported declarations in Main.lean share one central conclusion: for every positive modulus and every Dirichlet character, the associated L-function is nonzero when Re(s)>1/2, excluding the principal-character pole at s=1. Ordinary RH follows by specializing to modulus one and applying zeta’s functional equation. The critical-strip conclusions additionally use functional equations and the passage between primitive and imprimitive characters.

The source calls this central conclusion EveryCharacter. Its closing route is Main → MainTheorems → MainConclusion.everyCharacter → everyCharacter_of_row, with a proved Galois-representation/local-compatibility input. The arithmetic inputs and cohomological window theorem are assembled below that point.

This matters for reading the archive: five public endpoints are not five independent proofs. An imported module is also not automatically a mathematical dependency of a particular theorem. MainTheoremsAll imports additional small-class-number material, while the visible headline proof terms run through the shared EveryCharacter result. Determining the exact elaborated dependency closure requires proof-term analysis, not merely counting imports.

The checked scope is ordinary RH and GRH for Dirichlet L-functions. Names of directories involving Dedekind L-functions or automorphic forms do not enlarge that conclusion to every Dedekind, Hecke, or automorphic L-function.

Sources: [Main](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean), [MainTheorems](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean), [MainConclusion](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean).

## 2. Why the prime statistic has this exact form

For y≥1 the ordinary statistic is

$$
G(y)=\sum_{1\le n\le y}\Lambda(n)(y/n-1)
-y\log y+(1+\gamma_E)y.
$$

The von Mangoldt function weights prime powers. The ramp (y/n−1) vanishes at the moving endpoint, and its Mellin transform is elementary:

$$
\int_1^\infty (y/n-1)_+y^{-s-1}\,dy
=\frac{n^{-s}}{s(s-1)},\qquad \Re s>1.
$$

Combined with the Dirichlet series for the logarithmic derivative of zeta, this gives

$$
\Phi_\zeta(s)
=-\frac{\zeta'(s)/\zeta(s)}{s(s-1)}
-\frac1{(s-1)^2}
+\frac{1+\gamma_E}{s-1}.
$$

The subtractions cancel the principal singular terms at s=1. They are necessary analytic normalization. In the source, the regularization is implemented through (s−1)ζ(s), extended at s=1, together with its derivative there.

For a nonprincipal character χ, the analogous sum uses χ(n) and adds yL'χ(1)/Lχ(1). Its transform has the same denominator and an adjusted logarithmic derivative. This makes the prime sums compatible with a common analytic criterion.

At a zero ρ in the critical strip of multiplicity m, L'/L has residue m. The normalized transform consequently has a simple pole with residue −m/[ρ(ρ−1)]. Higher zero multiplicity increases the residue; it does not increase the transform's pole order.

Sources: [CharFamily](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean), [nonprincipal transform](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean), [zeta transform](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mellinGchiModOne.lean).

## 3. Three distinct uses of positivity

The arithmetic comparison produces a finite positive combination of real parts of character sums:

$$
G_F(y)=\sum_i a_i\Re G_{\chi_i}(y),\qquad a_i>0.
$$

The transform pairs each character with its inverse. At a zero of a constituent, the common residue is

$$
-\frac{S_\rho}{\rho(\rho-1)},\qquad
S_\rho=\sum_i\frac{a_i}{2}\left(m_i(\rho)+m_i^{\rm inv}(\rho)\right)>0.
$$

Positive coefficients therefore prevent cancellation of the pole. A complex residue need not be positive or even real. A pole on the positive real axis has a positive real residue because its location lies between zero and one.

Separately, the window criterion uses a nonnegative majorant R for G_F. It does not assume G_F itself is nonnegative.

These are different requirements: positive family coefficients prevent cancellation; the sign of a real-pole residue prevents a negative divergence from escaping a one-sided test; a nonnegative majorant controls positive mass. As an elementary diagnostic, choose 0<θ<β<1. Then g(u)=−exp(βu) has an identically zero upper majorant but a transform with negative residue at β. Removing the real-residue sign condition from the general theorem would make it false. This diagnostic is our own elementary example, not a defect reported in the submitted proof.

Sources: [poleData](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean), [PoleData and WindowHypU](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean).

## 4. The general window condition and the condition actually supplied

The general analytic theorem fixes 0<θ<1 and δ>0. For every η>0 and every threshold Y0, it asks for a Y≥Y0 and an integrable nonnegative majorant R≥G_F on the whole interval [Y,Y^(1+δ)] satisfying

$$
\int_Y^{Y^{1+\delta}}R(y)y^{-\theta-1}\,dy\le Y^\eta.
$$

The majorant and selected interval may depend on η and Y0. This controls weighted positive mass with arbitrarily small power losses.

A stronger pointwise bound G_F(y)≤Cy^θ on arbitrarily late whole windows implies the criterion: take R(y)=|C|y^θ and integrate to obtain |C|δ log Y, eventually smaller than Y^η. C is fixed before the successive windows are selected.

The actual arithmetic-to-analysis adapter uses this stronger pointwise form, with C=1. The final host-family construction supplies windows of the form [Y,Y^(3/2)]. Thus the weaker integral criterion explains the analytic machinery; it does not replace the concrete arithmetic obligation in the submitted route.

Neither finitely many samples nor an arbitrarily selected large point establishes a whole-window estimate. The order of quantifiers is also essential: the analytic proof chooses its tolerated loss after locating the hypothetical pole.

Sources: [WindowHypOfRpow](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/WindowHypOfRpow.lean), [actual formB adapter](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean).

## 5. Why sparse long windows can rule out a zero

Put y=exp(u), U=log Y, and g(u)=G_F(exp u). The window becomes [U,(1+δ)U], and the Mellin transform becomes a Laplace transform. Outside the selected interval, the abstract argument uses only a crude bound |g(u)|≤C0 exp(2u).

Normalized high derivatives satisfy

$$
A_k(s):=\frac{(-1)^k\Phi^{(k)}(s)}{k!}
=\int_0^\infty g(u)\frac{u^ke^{-su}}{k!}\,du.
$$

The source justifies differentiation under the integral. It chooses σ>2 sufficiently large, then an integer k near (1+δ/2)σU. The positive kernel u^k exp(−σu) is concentrated inside the selected interval; explicit tail bounds incorporate the crude global growth.

The one-sided estimate enters through the identity |g|+g=2 max(g,0)≤2R on that interval. This yields, simultaneously for every real t,

$$
|A_k(\sigma+it)|+\Re A_k(\sigma)
\le \frac{C e^{\eta U}}{(\sigma-\theta)^k}
$$

for arbitrarily large U with k≥U.

If a pole exists to the right of θ, the proof isolates a nearest pole at a suitable center. For nonreal poles, a small vertical displacement avoids ties in nearest distance; taking a norm removes the phase. A separate branch handles a real pole using its positive residue. Cauchy estimates bound the analytic remainder.

The contradiction has the explicit form

$$
\frac{c_0}{d^k}
\le \frac{M}{r^k}+\frac{Ce^{\eta U}}{E^k},
\qquad 0<d<r\le E=\sigma-\theta,\quad k\ge U.
$$

Choosing η=½ log(r/d)>0 makes the contribution from the nearer pole dominate exponentially. This is the concrete reason the one-sided whole-window hypothesis excludes a pole. A general statement that “zeros create oscillations” omits this mechanism.

Sources: [landauWindowIneq](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindowIneq.lean), [landauTails](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauTails.lean), [landauWindow](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean), [growth contradiction](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauGrowthContra.lean).

## 6. The actual arithmetic budget is more than x/m + m

The source's comparison theorem proves

$$
G_F(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}.
$$

The inspected final assembly uses e_D=2 and e_L=0, giving 1/2+9ε. Constants and loss exponents are fixed before x tends to infinity. Given a hypothetical zero with β>1/2, one can choose θ between 1/2 and β, then sufficiently small ε>0 with 1/2+9ε≤θ. An exact endpoint estimate at ε=0 is unnecessary.

The explicit intermediate error bracket is

$$
B=n_Ta\left(1+\frac{m^2}{k}\right)
+m\left(2nmbx^\varepsilon+
\frac{n_2kb x^\varepsilon}{n(nx^{-\varepsilon})}\right).
$$

Here n is the cardinality of the finite indexing group, n_T and n_2 are cardinalities of selected subsets, m is the chain length, k is an auxiliary rank parameter, and a,b are weight scales. Set d_T=n_T/n and d_2=n_2/n. Dividing by the positive comparison factor gives the exact identity

$$
\frac{B}{n_Tmbd_2/2}
=\frac{2a}{mbd_2}\left(1+\frac{m^2}{k}\right)
+\frac{4mx^\varepsilon}{d_Td_2}
+\frac{2kx^{2\varepsilon}}{d_Tn^2}.
$$

We checked this algebraic rearrangement independently. It displays inverse-density penalties and a k/n² term in addition to the familiar balancing terms.

The source supplies simultaneous constraints including

$$
a\le2xb,\quad d_T\ge\tfrac12x^{-\varepsilon/8},\quad
x^{-\varepsilon}\le d_2\le1,\quad
x^{1/2-\varepsilon}\le m\le x^{1/2+\varepsilon/2},\quad
xm\le k\le n^2x^{1/2-\varepsilon}.
$$

These constraints must hold together in this construction. Enlarging k reduces one error but increases another. A thin selected subset makes normalization expensive. Choosing a chain length alone does not control these effects.

More specifically, the parameter construction uses b=exp(x^ε), a=xb, a scale parameter Δ1=x^(−ε/8), and

$$
x^{1/2-\varepsilon/16}\le m\le2x^{1/2-\varepsilon/16},\quad
x^{2+8\varepsilon}\le n\le2x^{2+8\varepsilon},\quad
x^{9/2+10\varepsilon}\le k\le2x^{9/2+10\varepsilon}.
$$

Thus “about √x lifts” is an orientation with small exponent losses, not a claim that every object has dimension √x. Also Δ1 is not literally d_T: the source controls their ratio within fixed factors.

Sources: [CoreGm](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean), [TopShape](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean), [RankVal](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean), [full budget trace](traces/ARITHMETIC.md).

## 7. A source counterexample explains the amplified error budget

The strong error-window hypothesis requires

$$
(\bar\eta+4\sqrt{\bar e})x^{c_{HH}}b
\le Kx^\varepsilon(n_Ta).
$$

The source proves that replacing this with only the separate bounds bar_eta≤1 and bar_e≤1 is insufficient. Its explicit model takes x=100000, ε=1, b=1, a=k=x, m=n_T=1, B0=Nc=1, bar_eta=1, bar_e=0, and c_HH=10. The amplified contribution is at least x^10, while the proposed weak bound allows only x^5(x+3). These are incompatible.

The submitted argument uses the stronger product condition. The counterexample shows why an explanation must retain the scale that amplifies the small-looking errors. Our reproducibility script checks this final numerical inequality; it does not replay the Lean construction of all the model's hypotheses.

Sources: [ErrWindows and ErrWindowsWeak](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean), [error_sizes_weak_false](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean).

## 8. A reconstructed geometric subargument: projection, slope, covolume

One input controls a normalized logarithmic covolume. We traced this below its assembly wrapper to an arithmetic-lattice argument.

An orthogonal idempotent e splits the relevant directions into retained and discarded parts. For a lattice L these are L∩im(e) and L∩ker(e). A denominator condition g e(L)⊆L controls how the projection interacts with integrality.

Write d_g,d_b for their ranks, μ for the original arithmetic slope, and μ_g for the retained slope. The source first obtains

$$
(d_g+d_b)\mu\le d_g\mu_g+d_b(M+2\log g).
$$

With d_b≤3δ_b(d_g+d_b), 0≤δ_b≤1/12, M≤Q, μ≥−Q, and 0≤2 log g≤Q, elementary algebra gives

$$
\mu_g\ge\mu-12\delta_bQ.
$$

Small discarded rank is therefore useful only together with slope and denominator control.

In the application ε_z>0 is fixed, δ_b=exp(−x^(ε_z/7)), and Q=(x^A+x^B+C_1+C_2+1)E, with A,B,C_1,C_2 fixed before x grows. The source proves that 12δ_bQ≤E eventually. This produces the desired normalized covolume estimate

```math
\mathrm{lcv}_i/D\le T_i+(C_1+C_2+1)E.
```
The underlying geometric estimates that supply the rank cutoff, the maximum-slope envelope, and the initial lower bound remain deeper dependencies. What we have reconstructed is the projection-to-slope-to-covolume step and the explicit way its losses are absorbed.

Sources: [numeric and slope_good_ge](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MajAtAddRight.lean), [lcv_le and covolX_of_steps](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean).

## 9. The cohomological input explains why favorable intervals are needed

The source's Sha is a local-global kernel in first Galois cohomology for a cyclotomic twist of Q_l/Z_l. Its length is a module length over Z_l. This notation does not by itself identify an elliptic-curve Tate–Shafarevich group.

For the selected fields, VVle bounds, for every finite prime set S,

```math
\sum_{\ell\in S}\log\ell
\sum_{1\le r<t}\mathrm{length}_{\mathbb Z_\ell}
\Sha^1_\ell(E,r)
\le \exp(x^\varepsilon/2),
\qquad t=\lfloor x^{401}\rfloor.
```
The definition also requires the relevant lengths to be finite. VWin supplies this bound throughout a selected interval [Y,Y²] inside [X^(1/J),X], for all sufficiently large X, with J fixed earlier. Its field construction and auxiliary primes obey additional conductor, congruence, and splitting constraints.

This is a quantified bound on surviving obstructions. It does not assert that all such cohomology groups vanish. The bridge vvRecord turns uniformly bounded finite prime sums into a summable defect term; divinN_of_hypV then incorporates that defect into the divisibility budget.

At a deeper level, the window selection assembles Iwasawa-type bounds, Ferrero–Washington, local/global duality inputs, and counting estimates. We read the assembly and the finite-exception selection mechanism, not every theorem that supplies those ingredients.

A particularly clear sublemma defines a scale x as good if every exceptional index r≤x^Ct already satisfies r≤x^η. For 0<η≤Ct, X>1, and at most R exceptional indices, it constructs a whole [Y,Y²] with

$$
X^{1/J}\le Y,\qquad Y^2\le X,\qquad
J=2^{R+2}(C_t/\eta)^R.
$$

The proof moves to logarithmic coordinates and inducts on the finite exceptional set. It finds a multiplicative interval avoiding the intermediate range where exceptional indices would be costly. The number of exceptions can remain fixed while their locations depend on the outer scale X. This clarifies why the construction can provide arbitrarily late favorable windows without proving the same bound at every sufficiently large x.

Sources: [Sha and shaLen](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GaloisCohomology/Statement.lean), [VVle and VWin](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean), [DivinNOfHypV](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean), [Window](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window.lean), [Window1](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean), [ThmBabOfLemmaK](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ThmBabOfLemmaK.lean).

## 10. What “reflection” actually requires

For an imprimitive character, passing to its primitive inducing character introduces finitely many Euler factors 1−χ(p)p^(−s). They cannot vanish when Re(s)>0 because |χ(p)p^(−s)|<1. A zero therefore transfers to the primitive L-function.

The source checks Gamma-factor nonvanishing in the critical strip, applies the functional equation of the completed primitive L-function, and obtains a zero for the inverse character at 1−s. A zero left of 1/2 would then produce one right of 1/2, contradicting EveryCharacter. The zeta endpoint also handles s=0, the excluded trivial zeros, and the region Re(s)≥1.

These are standard ingredients, but their hypotheses are necessary. “Symmetry handles the other side” is a compressed description of this actual chain.

Source: [ClaimStrip](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean).

## 11. Present state of understanding

| Component | What this pass established | Remaining boundary |
|---|---|---|
| Endpoint statements | Read exact statements and shared closing route | No new full semantic/kernel audit here |
| Smoothed sums and transforms | Reconstructed normalization and zero-to-pole mechanism | Relies on imported foundational analysis |
| Localized Landau argument | Read derivative kernel, tail, pole-isolation, and contradiction proofs | No independent Lean replay |
| Arithmetic comparison | Located exact bracket, densities, rank constraints, and exponent losses | Still conditional on substantial geometric inputs |
| Error control | Read strong condition and explicit counterexample to its weakening | Not a complete audit of every budget term |
| Covolume | Reconstructed a projection/slope argument and eventual error absorption | Deep geometric estimates supplying the inputs remain only traced |
| Cohomological windows | Read exact length bound, assembly, and finite-exception interval lemma | Full Iwasawa, automorphy, and counting derivations remain unreconstructed |
| Theta-lift existence/nonvanishing | Located instantiated bundles and explicit existence calls | No complete human derivation of all local/global compatibility and divisibility inputs |

The [Lean/Mathlib joint statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) and [Sutherland's verification record](https://math.mit.edu/~drew/grh/) provide strong external evidence for the original formal result. The latter was last updated at 16:20 UTC on 22 November 2026 when retrieved. It records completed builds, module replay, independent export checks, statement comparison, and only the three standard axioms for the five endpoints. Some additional export-checking stages were still running.

That evidence is separate from our explanatory coverage. We have gained a substantive account of the analytic engine, the explicit comparison budget, one covolume argument, and the logic of interval selection. We have not yet reconstructed the full higher-rank automorphic and arithmetic-geometric construction. The author's own announcement treats parts of its narrative description as provisional. Keeping that distinction visible is necessary while the proof is being understood.

