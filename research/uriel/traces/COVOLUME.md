# A concrete covolume subargument in the original proof

Original source pin: `40e56bab026552e089d7afcfeff08d2defb9c005`. Source inspection only; no build or independent replay. This supplement goes below the top-level assembly to reconstruct a specific quantitative lemma.

## Route into the proof

The final theorem assembly `EveryCharacterOfLiteratureOfVWin.lean:810–813` supplies `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` as its covolume input. In the original `ThirdPlaceSeries/TopCovolSlim2Use.lean:16–22`, that theorem assembles geometric inputs and calls `topCovolG_alt_alt`. The original `TopCovolG.lean:39–60` assembles Gram, recursion, projection, bad-rank, size, maximum-slope, core-slope, and lower-slope estimates, then calls `covolX_of_truncation_badSet_lambda_lowBound`.

The latter is a wrapper around `ThirdPlaceSeries/CovolXOfSteps.lean:16–40`. That proof combines eventual bounds, chooses a common threshold, and invokes the substantive pointwise lemma `GlobalTheory.CovTop.Assembly.lcv_le` in `Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean:39–87`.

## What is being bounded?

`Formalism/QuotientMetricDivisors/Statement.lean:34–36` defines

$$
\operatorname{lcv}(X,L)=\frac{2}{[K:\mathbf Q]}\log\operatorname{ht}(X,L).
$$

This height is a normalized real covolume. `Formalism/HarderNarasimhan/StatementPl.lean:29–31` multiplies the covolume of the realized lattice by powers of 2 and the number-field discriminant. Thus the target genuinely controls a lattice's normalized logarithmic covolume; it is not a theorem that is only suggestively named “covolume.”

For a family point p and lift index i, define source abbreviations

$$
T_i=\operatorname{mainT}(p,i)=p.Z.l3m(i),\qquad E=\operatorname{unitE}(p)=p.Z.l3u.
$$

The precise pointwise target is

$$
\frac{\operatorname{lcv}((p.S\;\mathrm{false}).XW_i,
 (p.S\;\mathrm{false}).M_i)}{(p.S\;\mathrm{false}).D}
\le T_i+(C_1+C_2+1)E.
\tag{C}
$$

`Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:315–316` defines the obligation `L3` to be exactly the corresponding collection of bounds for all indices. `ThirdPlaceSeries/LiftLambdaBound.lean:60–61` defines `CovolumeBoundOfX` as an eventual uniform bound of this shape, valid for every qualifying point and for every C above some fixed C0. `EventualL3OfCovolume.lean:14–20` transfers it to the selected summands used downstream.

I have not independently reduced T_i and E to all the final prime-sum parameters. That is a separate dependency trace; (C) alone is not the square-root estimate for prime sums.

## The good-subspace estimate

The source constructs a type lattice L and an idempotent e. Its good and bad lattices are explicitly

$$
L_g=L\cap\operatorname{im}(e),\qquad L_b=L\cap\ker(e)
$$

(`Definitions/Divisors/NormNegCmConstantEqAtAllEmbeddings.lean:41–48`). At every complex embedding, the idempotent obeys a Pythagorean norm identity, hence is orthogonal for the relevant Hermitian metric. It is not assumed to preserve the lattice integrally: an integer g controls the denominators, with g e(L) contained in L.

`Proofs/DivisorProofs/MajAtAddRight.lean:111–142` proves `slope_good_ge`. Write d_g,d_b for the good/bad ranks, mu for the normalized type-lattice slope, mu_g for the good-lattice slope, m for an upper slope bound, and ell=2 log g for the denominator cost. Under the source's Gram, finite-generation, nonzero-lattice, orthogonality, and integral-denominator hypotheses, it uses the rank-weighted inequality

$$
(d_g+d_b)\mu\le d_g\mu_g+d_b(m+\ell).
$$

Assume additionally

$$
0\le\delta\le\tfrac1{12},\quad
d_b\le3\delta(d_g+d_b),\quad
m\le Q,\quad-\mu\le Q,\quad0\le\ell\le Q.
$$

Then d_b <= 4 delta d_g, and therefore

$$
\mu-\mu_g
\le\frac{d_b}{d_g}(m+\ell-\mu)
\le4\delta\cdot3Q=12\delta Q.
\tag{P}
$$

This is the exact reasoning of the separate arithmetic lemma `numeric` at lines 93–109. A small discarded rank alone is insufficient: the maximum-slope, lower-total-slope, and denominator bounds are also essential. The proof derives positive good rank before dividing.

The preceding `selfAdj_of_pyth` proof (lines 55–89) is also substantive: it first obtains zero real cross-term from Pythagoras; multiplying one vector by a field element with a nonreal embedding eliminates the imaginary cross-term; it then derives self-adjointness. This uses the totally complex field hypothesis.

## How the estimate becomes (C)

The definitions in `Definitions/Divisors/CovolXOfCovol.lean` give:

1. `RecAt`, lines 57–59: lcv/D <= -mu_g.
2. `CoreAt`, lines 92–94: mu_type >= mu_core-C1 E.
3. `LowAt`, line 96: mu_core >= -T_i-C2 E.
4. `BadAt`, lines 69–71: discarded rank <= 3 exp(-x^(ez/7)) times type rank.
5. `LamAt` and `SizeAt`, lines 73–80: fixed power-growth size and maximum-slope envelopes, E>=b>=1, and controls on T_i and the denominator cost.

The pointwise proof sets

$$
\delta=\exp(-x^{\varepsilon_z/7}),\qquad
Q=(x^A+x^B+C_1+C_2+1)E.
$$

Combining (P) and the preceding inequalities gives

$$
\frac{\operatorname{lcv}}D
\le-\mu_g
\le-\mu_{\mathrm{type}}+12\delta Q
\le T_i+(C_1+C_2)E+12\delta Q.
$$

For fixed A,B,C1,C2 and positive epsilon_z, the final loss is at most E once x is sufficiently large:

$$
12e^{-x^{\varepsilon_z/7}}
(x^A+x^B+C_1+C_2+1)\le1.
$$

This supplies (C). `CovolumeFromGramAndBounds.lean:17–33` explicitly proves the necessary exponential-times-power convergence and extracts the threshold. The family-level assembly uses the maximum of this threshold and the thresholds for all input estimates, so they hold simultaneously. Constants/exponents are selected before x; allowing arbitrary x-dependent exponents would invalidate this absorption argument.

## What is understood versus what is still assembled

This pass reconstructs the quantitative projection/slope mechanism and its exponential error absorption directly from proof bodies. It identifies why a sparse bad component can be discarded without losing control of the desired lattice's covolume.

The deeper geometric work that supplies the input estimates is still largely represented by assembly in this pass. In `TopCovolG`, the `low` bound is built from deep coverings, descent maps, rank comparisons, bounded generators, flatness, a uniform lower bound, and lower bounds on heights. `HeightLowerBoundGeneral.lean` further supplies geometric and short-section data to `height_of_meanAll_bound`, including a section controlled by a Bergman kernel. I inspected those connections but have not independently reconstructed the arithmetic Hilbert–Samuel, intersection-theoretic, or automorphic arguments proving all those ingredients.

Consequently, the verified explanatory statement is local and precise: given these established inputs, the final covolume estimate follows through the displayed slope calculation. Claiming that this alone explains the entire self-intersection theorem or the novel arithmetic core would go beyond this reading.
