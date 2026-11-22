# Analytic source reconstruction

Original source pin: `40e56bab026552e089d7afcfeff08d2defb9c005`. These notes reconstruct selected source proof bodies, not an independent kernel replay or an audit of the complete arithmetic construction. All file paths below are relative to `src/`. Source locations refer to the original pin, not the community checkout.

## 1. The actual analytic hypothesis is weaker than our first summary

Write `G_F(y) = sum_i a_i Re G_chi_i(y)`, where the finite family's weights are strictly positive. The family admits only nonprincipal characters, except that the principal character of modulus one is allowed. No conjugation closure of the supplied family is required: the transform construction explicitly symmetrizes each character with its inverse.

The general `WindowHyp F theta delta` requires, for every `eta > 0` and every threshold `Y0`, some `Y >= Y0` and a nonnegative majorant `R` on `[Y,Y^(1+delta)]`, with `G_F <= R`, such that

$$
\int_Y^{Y^{1+\delta}}R(y)y^{-\theta-1}\,dy\le Y^\eta.
$$

The weighted majorant must be integrable on that window. Theta and delta are fixed before eta and the threshold; delta must be strictly positive. Windows and majorants may depend on eta and the threshold. This is an arbitrarily small power loss on the *weighted positive mass*, not a global absolute-value estimate on `G_F`.

The simpler pointwise condition `G_F(y) <= C y^theta` across arbitrarily late whole windows implies this by choosing `R=|C|y^theta`: its weighted integral equals `|C| delta log Y`, eventually at most `Y^eta`. This is exactly the proof of `windowHyp_of_rpow`. The constant C must remain fixed as the selected window moves.

Crucially, the actual downstream adapter **does** use this stronger pointwise form: `PrimitiveCosets/Imports.lean`, `UpperTheory.Comparison₂.formB`, lines 9–20, calls `zeroFree_of_rpow_window` with `delta = la - 1` and `C = 1`. `PrimitiveCosets/LevelFamily.lean` constructs a strictly positive family from `Level.KEPT`, identifies its sum with `Level.Gm`, and identifies its zero-free predicate with `Level.ZeroFreeAbove`. Therefore do not replace the arithmetic obligation by an unsupported assertion that only the weaker integral bound is what the arithmetic proof actually supplies.

Sources: `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean` lines 24–45; `LandauTheorems/WindowHypOfRpow.lean` lines 27–57; `LandauTheorems/ZeroFreeOfRpowWindow.lean` lines 11–14.

## 2. Why this particular smoothed prime sum appears

For nonprincipal chi let c_chi = L'_chi(1)/L_chi(1). The source defines

$$
G_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)(y/n-1)+c_\chi y.
$$

For zeta, the correction is `-y log y + (1+EulerGamma)y` instead. The ramp is the positive part `(y/n-1)_+`, written as a finite sum. Its elementary Mellin transform for `Re s > 1` is

$$
\int_1^\infty (y/n-1)_+y^{-s-1}dy=\frac{n^{-s}}{s(s-1)}.
$$

Summing and using the von Mangoldt Dirichlet series gives

$$
\Phi_\chi(s)=\int_1^\infty G_\chi(y)y^{-s-1}dy
=-\frac{L'_\chi(s)/L_\chi(s)-s c_\chi}{s(s-1)}.
$$

For zeta the corresponding expression is

$$
\Phi_\zeta(s)=-\frac{\zeta'(s)/\zeta(s)+(s-1)^{-1}+1-(1+\gamma_E)s}{s(s-1)}.
$$

The normalization cancels the unwanted behavior at s=1. `poleData_char` constructs the entire regularization f(s)=(s-1)zeta(s), updated to f(1)=1, proves f'(1)=EulerGamma, and applies an abstract logarithmic-derivative construction. This is much more informative than merely saying the prime sum is “related to the zeros.”

Sources: `CharFamily.lean` lines 10–22; `LandauTheorems/mellinGchiOfNeOne.lean` lines 116–142; `LandauTheorems/mellinGchiModOne.lean` lines 115–199; `LandauTheorems/poleData.lean` lines 137–239. `MellinRamp.lean` is the elementary ramp identity dependency.

## 3. Every zero becomes a noncancelling simple pole

At a zero rho in the critical strip of multiplicity m, the logarithmic derivative has the local form

$$
L'(s)/L(s)=m/(s-\rho)+h(s),
$$

with h analytic. Thus the transform has a simple pole even if L has a multiple zero. Its residue is `-m/[rho(rho-1)]`. For the real-valued family sum the transform is

$$
\Phi_F(s)=\sum_i\frac{a_i}{2}(\Phi_{\chi_i}(s)+\Phi_{\chi_i^{-1}}(s)).
$$

At a zero of any constituent (or its conjugate) the residue is

$$
c_\rho=-\frac{S_\rho}{\rho(\rho-1)},\qquad
S_\rho=\sum_i\frac{a_i}{2}(m_i(\rho)+m_i^{\rm inv}(\rho))>0.
$$

All multiplicities are nonnegative and at least one is positive, so the common complex factor cannot cancel. This does **not** make the residue a positive real number at every complex zero. The abstract `PoleData` assumption asks additionally that a pole on the positive real axis have a positive real residue. Here a real zero must lie between zero and one, giving that positivity.

The distinction is essential. For the abstract model `g(u)=-exp(beta u)` with `0<theta<beta<1`, the transform has a negative-residue real pole although g satisfies trivial one-sided upper bounds; a theorem omitting real-residue positivity would be false. This counterexample is our direct mathematical explanation of the hypothesis, not a source-reported defect.

Sources: `LandauTheorems/LogDerivLocal.lean` lines 9–39; `LandauZeroFreeCriterion.lean` lines 15–23; `LandauTheorems/poleData.lean` lines 248–400, especially positive S and the real-pole calculation near the end.

## 4. The actual Landau argument uses localized high derivatives

Change variables `y=exp u`, set `g(u)=G_F(exp u)` and `U=log Y`. The window becomes `[U,(1+delta)U]`, the weighted integral becomes

$$
\int_U^{(1+\delta)U} R(e^u)e^{-\theta u}du\le e^{\eta U},
$$

and the Mellin transform becomes a Laplace transform. A crude global growth bound `|g(u)| <= C0 exp(2u)` is enough outside the favorable window; there is no global square-root estimate being silently assumed.

For sigma>2 define

$$
A_k(s)=\frac{(-1)^k\Phi_F^{(k)}(s)}{k!}
=\int_0^\infty g(u)\frac{u^k e^{-su}}{k!}du.
$$

`IteratedDerivLaplace.lean` justifies differentiation under the integral using explicit local domination, then induction. `LandauCoeff.lean` transfers it to Phi.

The positive kernel `u^k exp(-sigma u)/k!` peaks near `u=k/sigma`. `landau_tails` chooses sigma sufficiently large as a function of delta and

$$
k=\lceil(1+\delta/2)\sigma U\rceil.
$$

This centers the kernel in the favorable logarithmic window. Explicit Chernoff-style estimates, including the crude exp(2u) growth, control the two tails by `C/sigma^k`. The formal lemma also ensures k>=U.

The key inequality is obtained from `|g|+g=2 max(g,0)<=2R` **on the window**. It does not assume g itself is nonnegative. After incorporating tails and the weighted mass estimate, `landau_window_key` gives a fixed sigma>2 and C such that, for every eta>0, arbitrarily large U admit a k>=U with, simultaneously for every real t,

$$
|A_k(\sigma+it)|+\operatorname{Re}A_k(\sigma)
\le \frac{C e^{\eta U}}{(\sigma-\theta)^k}.
$$

This norm-plus-real-part combination is how a one-sided upper bound on g constrains complex singularities despite potentially large negative values.

Sources: `LandauTheorems/WindowHypUOfWindowHyp.lean` lines 29–56; `IteratedDerivLaplace.lean` lines 48–105; `LandauCoeff.lean` lines 10–28; `landauWindowIneq.lean` lines 27–111; `landauTails.lean` lines 80–131; `landauWindow.lean` lines 40–73.

## 5. Why a pole right of theta contradicts the kernel bound

The proof does not simply assert that zeros “cause oscillations.” It isolates a pole and compares two exponential rates of high derivatives.

The discrete pole set permits a geometric dichotomy. Either a disk around the real center sigma is pole-free and a suitable vertically shifted center sigma+it has a unique closer pole, or there is a uniquely nearest real pole beta>theta. In the first case `landau_nearest` avoids a finite set of vertical heights at which two candidate poles tie for nearest distance. In the second case positive real residue supplies the needed sign.

For an isolated simple pole rho of residue c, Cauchy estimates on the analytic remainder yield

$$
A_k(z)=\frac{c}{(z-\rho)^{k+1}}+O(r_1^{-k}),
$$

where `r1` is a positive radius with `d=|z-rho|<r1`. Without O notation, the source proves an error at most `M/r1^k`. The radii can be chosen with `d<r1<=sigma-theta`. The pole contribution therefore dominates the allowable derivative bound and the analytic remainder exponentially as k grows. Relabeling this intermediate radius e, combining the bounds forces

$$
\frac{c_0}{d^k}\le\frac{M}{e^k}+\frac{C e^{\eta U}}{E^k},
\qquad 0<d<e\le E=\sigma-\theta,
$$

for arbitrarily large U and k>=U, with c0>0. The source selects `eta = (1/2) log(e/d)`. Exponential separation `(e/d)^k` outruns that allowed loss, giving a contradiction. Hence every pole has real part at most theta.

Sources: `LandauDichotomy.lean` lines 24–87; `LandauNearest.lean` lines 36–109; `LandauPoleAsym.lean` lines 19–79; `LandauCauchy.lean` lines 9–33; `LandauGrowthContra.lean` lines 9–40; `landauWindow.lean` lines 83–166.

## 6. Completing the analytic implication, and the actual final wrappers

`lemmaL` combines `poleData`, the logarithmic change of variables, and `landau_window`. A putative zero with theta<Re(s)<1 belongs to the pole set and contradicts its bound. Zeros at Re(s)>=1 are excluded by the already-established character nonvanishing theorem. The theorem requires `0<theta<1`, `delta>0`.

To conclude RH from bounds for every theta>1/2, a hypothetical zero beta>1/2 allows choosing theta strictly between 1/2 and beta. The theorem does not prove the endpoint estimate at theta=1/2. Functional equations then exclude zeros to the left.

Actual final source path: `Main.lean` -> `Supplements/Kernels/MainTheorems.lean` -> `CharacterBoxes/MainConclusion.lean` -> `ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` (810–813) -> `SiegelEisensteinSecondTermHypotheses.lean` -> `UpperTheory.Top.every_character_of_green_v_win`. The arithmetic-to-window part between this path and `Comparison₂.formB` is treated separately in [ARITHMETIC.md](ARITHMETIC.md); this analytic trace does not independently reconstruct those arithmetic inputs.

For all Dirichlet characters, the final strip wrapper first passes an imprimitive character to its primitive character. The finite omitted Euler factors cannot vanish for Re(s)>0 because their nonconstant terms have norm strictly below one. It then uses the completed primitive L-function functional equation to move s to 1-s and invert the character. Gamma-factor nonvanishing in the strip makes this transfer legitimate. The five advertised final theorems are therefore closely related wrappers around `EveryCharacter`, not five independently derived proofs.

Sources: `LandauTheorems/lemmaL.lean` lines 13–22; `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`; `Formalism/GammaFactorNonvanishing/CritLine.lean`; `Formalism/GammaFactorNonvanishing/RhOfRight.lean`; `Supplements/Kernels/MainTheorems.lean`.

## Boundaries and corrections to our earlier presentation

- Pointwise whole-window control is a strong sufficient condition; the general analytic theorem is a weighted positive-mass criterion. The actual formB adapter uses the stronger form with constant one.
- Positive family weights, positive real-pole residues, and nonnegative window majorants are three different uses of positivity; they should not be conflated.
- Main-term subtraction is purposeful analytic regularization, not cosmetic normalization.
- The logarithmic window has length delta U. Fixed positive delta and arbitrarily large U are what permit a concentrated high-derivative kernel and an exponential contradiction. A finite sample, one bounded window, delta=0, or one fixed loss eta would not establish the stated result.
- Reading these explicit proof bodies gives a more substantial analytic explanation. It does not establish that every arithmetic input producing the windows has been independently understood or rechecked.
