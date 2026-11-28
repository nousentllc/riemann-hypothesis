# Arithmetic-to-prime-sum source trace

Source inspected: original commit `40e56bab026552e089d7afcfeff08d2defb9c005` of `leanprover-community/riemann-hypothesis`. All readings used `git show` at that pin. No Lean build or proof replay was run. The mathematical normalization below was additionally checked with SymPy; this checks the algebraic rearrangement only.

## Main result of this reading

The arithmetic-to-analytic passage has an explicit, considerably richer bound than the earlier illustrative `x/m + m`. We can now identify the actual bracket, its normalizing factor, the required density/rank inequalities, the exponent loss, and a source-level counterexample showing why an apparently mild weakening of an error assumption fails. We have also followed the final proof's explicit assembly calls back to conditional existence theorems for compatible arithmetic bundles. We have not unpacked all the local/global automorphic construction behind those theorems.

## Direct final route, distinguished from older parallel wrappers

`Main.lean` proves its five declarations through `Supplements/Kernels/MainTheorems.lean`: `allChi` calls `UpperTheory.FinalTheorems.everyCharacter`. `CharacterBoxes/MainConclusion.lean` feeds the proved `galoisLocalGlobalStrong_recParameter` into `everyCharacter_of_row`; this calls `every_character_of_literature_of_vWin` with an `OpenLiteratureStatements` bundle and `vwin_of_row`.

At the next level, the original direct route is:

1. `ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`: `every_character_of_literature_of_vWin` packages the local and global theorem inputs, supplies the covolume estimate, and calls the next theorem.
2. `ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69–74`: `every_character_of_theta_integrals_local_matching` requires `UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs`, equality of theta integrals, local matching, a covolume bound, local Langlands parameter existence, and `VWin`.
3. In the same file, `nonempty_hyps_definite_side_of_closed_bound` proves nonemptiness of `HypsAlt` by combining rationality, an evaluation grid, nonvanishing/low-weight and functional bounds, and linked covolume data. It calls `hypotheses_nonempty_of_unramified_exponents_alt`.
4. `ThirdPlaceSeries/TopPlug.lean:12–18`: `zero_free_all_of_green_v_win` and `every_character_of_green_v_win` instantiate the window ratio `la = 3/2`, use `shape_closed_link_n_of_green`, and obtain the character-specific host supply from `supplyChi`. The last step passes primitive nonvanishing to all characters using `imprimitive`.
5. `ThirdPlaceSeries/TopShape.lean:33–56`: `shape_closed_link_n_of_green` assembles divisibility, comparison, irreducibility, rank, and global constraints and calls `topDesWin` with `Cabs=2`, `C0=3`, `eD=2`, `eL=0`.
6. `CharacterBoxes/DesWin.lean:11–33`: `topDesWin` aligns the finitely many eventual conditions into a common family; constructs the divisibility input using `divinN_of_hypV`; and obtains `FamilyClassConnected`.
7. `CharacterBoxes/ZeroFreeAllOfTopG.lean`: `zeroFreeAll_of_topG` extracts the connected family and invokes `zeroFreeOn_of_tiedWin_cyc`, supplying `level_gm_le_on_family_scales` and `formB`.
8. `PrimitiveCosets/LevelGmLeOnFamilyScales.lean:13–30`: `tiedCore_of_chainTied` extracts the concrete `CoreAtH` data from `ChainTied`; `level_gm_le_on_family_scales` applies `windowInequality_of_artinInputs`.
9. `PrimitiveCosets/WindowInequalityOfArtinInputs.lean:17–26`: `windowInequality_of_artinInputs` combines the eventually valid host and chain bounds with `core_gm` at each point in the family windows.
10. `PrimitiveCosets/CoreGm.lean:12–72`: `core_gm` combines `ch_top`, `ch_core`, character compatibility (`charsA`, `gmA_eq`) and the remainder bound `sigA_le`.

The old `CharacterBoxes/EveryCharacter.plugAll` and `ShapeWin.shapeWin` are also present. They are not the names directly called by the original final `MainConclusion` route; the `ThirdPlaceSeries` wrappers above are. Both routes converge on the same `topDesWin` and comparison infrastructure.

## The explicit bound

The original `core_gm` statement is:

$$
\Lambda.G_m(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}.
$$

Here `Λ` is a `Level`, not the von Mangoldt function. `Gm` is the appropriate character-family prime-sum combination. The eventual threshold depends on the fixed level and constants. The theorem quantifies these constants before `x`, so they are not freely retuned at every point.

Because the inspected final `TopShape` call uses `eD=2`, `eL=0`, this route gives the exponent `1/2 + 9 ε` on its supplied windows. This is an exponent-loss bookkeeping result. It does not establish an estimate at exactly exponent `1/2`; the later argument chooses a sufficiently small positive `ε` for any target exponent above `1/2`.

### The actual error bracket

`Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:133–136` defines, writing `n=|H|`, `n_T=|TT|`, `n_2=|T2|`,

$$
B=n_T a\left(1+\frac{m^2}{k}\right)
 +m\left(2nmbx^\varepsilon+
 \frac{n_2 k b x^\varepsilon}{n(nx^{-\varepsilon})}\right).
$$

`DedekindLFunctions/LandauTheorems/ChTop.lean:37–74` proves a pointwise bound on `gapA` by `x^{C_E ε}B`, where `C_E=eDiv+eLoss+3`. It identifies `gapA = ASK - Main`, invokes `each_unit_bound_statement`, then bounds the entire resulting error using `errX5at_le`.

`ChCore.lean:283–340`, the lemma `CharacterBalanceMoves.core`, uses finite-character orthogonality and thick/thin weight controls to obtain

```math
n_T m b\frac{\delta_2}{2}\,Y
\le \mathrm{Err}+\frac{2n_Tmb}{x},\qquad
\delta_2=\frac{n_2}{n}.
```
The `Y` supplied later is the retained prime-sum combination minus explicit remainder and movement errors. The normalizer is positive only after the cardinality, rank and positive-weight conditions are supplied.

Set `δ1=n_T/n` for this displayed identity only; this is the actual density, not the source’s `Scale.delta1`. A direct algebraic rearrangement of the actual bracket gives

$$
\frac{B}{n_Tmb\delta_2/2}
=\frac{2a}{mb\delta_2}\left(1+\frac{m^2}{k}\right)
 +\frac{4mx^\varepsilon}{\delta_1\delta_2}
 +\frac{2kx^{2\varepsilon}}{\delta_1n^2}.
$$

This identity was verified by SymPy simplification, with residual exactly zero. It makes the earlier balancing story more precise: `x/m` and `m` really do appear after using `a≈xb`, but there are inverse-density penalties, a `k/n²` term, and the independent exponent factor `x^{C_E ε}`. Selecting `m≈sqrt(x)` controls only part of the problem.

Notation warning: `δ1` here denotes the actual density `n_T/n`. The source's `Scale.delta1` is instead the prescribed scale `x^(-ε/8)`; `HostVal` compares the actual density with that scale within a factor two. They should not be silently identified.

### Required size relations and how the square-root exponent survives

`SChain.lean:53–59` (`RestSize`) and `GrowthBoundGivesRiemannHypothesis.lean` (`SizeWindows`) impose:

$$
\begin{gathered}
a\le 2xb,\qquad
\delta_1\ge \tfrac12x^{-\varepsilon/8},\qquad
x^{-\varepsilon}\le\delta_2\le1,\\
x^{1/2-\varepsilon}\le m\le x^{1/2+\varepsilon/2},\qquad
xm\le k\le n^2x^{1/2-\varepsilon}.
\end{gathered}
$$

These are simultaneous obligations. In particular, choosing a small `m` worsens `x/m`; choosing too large an `m` worsens the second term; sparse `TT,T2` worsen the normalized estimate; a large `k` helps `m²/k` but worsens `k/n²`.

The actual selected scales are more informative still. `Formalism/LocalRingCardinality/DataParams₂.lean` defines `b=exp(x^ε)`, `a=xb`, and `Scale.delta1=x^(-ε/8)`. `GlobalTwisting/PairRowIffQdRows.lean` (`RankVal`) gives `n≈x^(2+8ε)`, `m≈sqrt(x Scale.delta1)=x^(1/2−ε/16)`, and `k≈x^(9/2+10ε)`, with each approximate relation bounded above by twice the displayed power. `Formalism/LocalRingCardinality/Params.lean` defines the tower rank `Ranks.N(j)=k+j(t+1)` and the signatures `sigW(j)=(k+j−1,m−j)`. Thus the square-root scale concerns the number of chain stages; it does not mean that all auxiliary groups or representations have square-root size.

`ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507–592`, `proposition_size_bound`, explicitly bounds the four unnormalized bracket terms by `2,2,4,2` times

$$
x^{1/2+13\varepsilon/8}\,(n_Tmb).
$$

It absorbs division by `δ2` using `δ2≥x^{-ε}`, obtaining a bound with factor `26` and exponent `1/2+(C+21/8)ε`. The hypothesis `26≤x^{3ε/8}` absorbs that numerical constant, yielding `1/2+(C+3)ε`. `CoreGm` adds the final character-remainder absorption, yielding `eD+eL+7`.

## What supplies the gap bound

`SChain.lean:17–20` defines `SizeData₂` as eleven conditions: positive Hida-setting data, divisibility, exponent comparison, height comparison, count bounds, slopes, quotient-slope bounds, losses, a slope inequality, a height bound, and parameter control. Thus `ch_top` does not get the necessary gap inequality merely from sizes.

`MeanBoundSecondForm.lean:116ff` defines the divisibility condition as an inequality between arithmetic slopes/heights and a main term, with errors `cDiv n_T a La` and `cDiv m(B0+Nc)x^{eDiv ε}`. `QuotientSlopeBoundsWith.lean` gives the other exact error terms.

`ChainSlopeWindows/LevelOfCongruence.lean:175–200` proves `each_unit_bound_statement` by combining a lower bound on the weighted slope, a bound on its variation, a count bound for `T`, upper/lower quotient slopes, and the loss estimates. `PChain.lean:613–672` then proves `errX5at_le`, bounding all terms by `x^{(eDiv+eLoss+3)ε} ErrText`, where

```math
\mathrm{ErrText}=n_Ta(1+m^2/k)+m(B_0+N_c).
```
The `BNBounds` conditions substitute explicit estimates for `B0,Nc`, producing `B` above. This is the visible point where arithmetic/cohomological defects are converted into the final analytic budget.

## A genuine source-level counterexample to a weaker explanation

The strong `ErrWindows` condition includes

$$
(\bar\eta+4\sqrt{\bar e})\,(x^{c_{HH}}b)
\le Kx^\varepsilon(n_Ta).
$$

Controlling `bar_eta` and `bar_e` alone is insufficient because the potentially large factor `x^{cHH}b` amplifies them.

`ChainSlopeWindows/SubThreeMulLogTwoLe.lean:471–488` proves `error_sizes_weak_false`: the same claimed bound is false if this product condition is replaced with only `bar_eta≤1`, `bar_e≤1`. Its explicit model uses `x=100000`, `ε=1`, `a=k=100000`, `b=1`, `m=n_T=1`, `B0=Nc=1`, `bar_eta=1`, `bar_e=0`, and `cHH=10`; the claimed multiplier is only `x^5`. The proof obtains the lower bound from `error_lower_eta`, combines it with the hypothetical weak upper bound, and finishes by numerical contradiction. This is not a counterexample to the RH proof: the final route uses the stronger condition. It is a concrete counterexample to dropping a crucial hypothesis from an explanation.

## Existence is located, but not yet reconstructed completely

`ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41–64` proves the nonempty hypothesis bundle through three substantive components: compatible member bundles with large unramified exponents; all required rows/constraints for those bundles; and common family selection.

`MemberBundlesLargeUnramifiedExponents.lean:34–61` proves the first component using explicit invocations of compatible-system/member hypotheses, rational weights, saturation at weight one, multiplicative closure, base-lattice existence and a nonzero Weil block. `NonemptyHypsOfAllRows.lean:19–100` assembles the row constraints and supplies the actual `hEx` field at line 59. `TopShape` then obtains a common design using the `designExists_of_tuSize_aux4n_litThin` wrapper; the underlying `DesignExistsOfChoices.lean:54–72` combines thresholds using a common supremum of requirements.

This is beyond reading `RankVal`: the source does contain explicit existence calls and a mechanism to satisfy many eventual conditions simultaneously. But names such as `compatibleSystem_weilBlock_ne_alt` or the packaged published results are still unresolved explanatory dependencies in this reading. We cannot yet claim a fully reconstructed number-theoretic account of why the theta-lift chain is nonzero and has exactly the needed integral divisibility, height and local compatibility properties.

## Epistemic boundary

- High confidence in the quoted declarations, formulas and visible call chain: read directly at the original pin.
- High confidence in the normalized bracket identity: independently simplified symbolically.
- Conditional understanding of why the explicit budget implies the square-root-plus-epsilon bound: source proof read, elementary steps reconstructed.
- Incomplete understanding of the automorphic construction and all imported proof bodies that discharge the hypotheses. Locating their existence theorems is not the same as understanding their proofs.
- No new conclusion about correctness of the entire archive from this source trace alone; no full kernel replay here.
