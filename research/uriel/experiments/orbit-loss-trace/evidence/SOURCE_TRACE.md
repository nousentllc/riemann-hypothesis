# How an omitted top enters the global bound

The fixed source is the Git tree at `40e56bab026552e089d7afcfeff08d2defb9c005`. Each citation links to that version. The accompanying manifest records the pinned Git blob and an independent SHA-256 digest of the extracted bytes. Descriptions of theorem bodies below are source readings. Strengthened bounds are explicit mathematical deductions unless separately replayed in a supplement. None of the quantities below is a measured omitted mass for the conductor-one host.

## From selected points to a counted omission

Fix the host, the data at its scale, and its top set $TT$. For each prime $p$, the source filters $TT$ by the failure of `Good` for the orbit representative determined by that particular $p$ and top. Then it sums the failed-top counts with weight $\log(p)/p$ over the selected residue primes of sufficiently large order. Write this mass as $B$. The normalized contract `ChBadp_at` requires $B\le T x^{-2+\varepsilon}$ with $T=|TT|$. The other contract `ChBad_at` has a different right side involving $C_b$, rank, density and the total prime weight. [Bad tops and the two contracts][chosen1] · [Normalized contract][chosenp1]

The per-family bridge preserves cardinality under transport to $TTv$ and identifies each filtered count with the original $|\mathrm{badTops}(p)|$. A separate implication maps every omitted top of a *served* prime to a counted bad top and places that prime in the chosen prime set. In particular the bridge needs both the weighted bound and the coverage of omissions. A bad top that was retained can contribute to $B$ without contributing to the omission. [Cardinality identities][ties1] · [Bridge and coverage][ties2] · [Joint hypotheses][budget4]

`out_discriminant_bound` uses that inclusion, the nonnegative weights, and enlargement of a prime sum. For $m=|J|$, $a\ge0$, and any valid upper bound $R$ for $B$, it gives
$$
O=\sum_{p\;\mathrm{served}}4ma\,\frac{\log p}{p}|TT\setminus TT_p|\ \le\ 4amB\ \le\ 4amR.
$$
Thus $B=0$ forces $O=0$. The hypotheses on primes ensure that each weighted omitted count at a served prime has positive prime weight. The inequality alone, with $m=0$, does not imply that the omitted sets themselves vanish, although their inclusion in the zero weighted bad set still does so under the prime hypotheses. [Pointwise and summed comparison][consumer1] · [Abstract contracts][budget2]

### How the normalized orbit bound is obtained

At the host, $B\le4 C_b x^{-2}\delta n W$ where $W$ is the sum of the eligible prime weights. The family transfer recovers the same top set and Frobenius labels after identifying ranks, using injectivity of their numeric labels. The canonical-base condition identifies the computed representative. Equal cardinalities alone would not justify this transfer. [Host condition and canonical representatives][host1] · [Same-host transfer][host2]

With the top-density lower bound $\delta n\le2T$ and $C_b\ge0$, two source arguments can be compared at fixed $C_b$. The host argument first sums over **all integers** below $X'$ and bounds $W\le2 x^{2\varepsilon/3}$. The chosen-family argument instead retains primality and bounds $W\le2x^{\varepsilon/3}$. Before constant absorption these give $B/T\le16C_b x^{-2+2\varepsilon/3}$ and $B/T\le16C_b x^{-2+\varepsilon/3}$ respectively when $T>0$. They yield the common normalized upper budget eventually. At $C_b=1$, $\varepsilon=1/64$, the two sufficient scales for *this absorption alone* are $2^{768}$ and $2^{384}$. The host theorem uses $|C_b|$ and supplies an explicit sufficient cutoff; the family construction takes additional thresholds. [Harmonic majorization][harm1] · [Host consequence][harm2] · [Chosen family hypotheses][primew1] · [Prime-specific estimate][primew2]

## Where the scale factors cancel

The first multi-term discriminant ledger is `tDetD`. Its eleven summands include `tOutD`, the cap obtained with $R=T x^{-2+\varepsilon}$. Its scale is $U=Tmb$ with $a=xb$. Consequently $\mathrm{tOutD}=4x^{-1+\varepsilon}U$. This equality also holds for zero volume. In quotients below, assume $U>0$. At $K\ge1$, its coefficient divided by $\mathrm{sg}=100Kx^{-1+4\varepsilon}$ is $1/(25Kx^{3\varepsilon})$. [Original scales][scale1] · [Units and coefficients][window3] · [Eleven-term budget][budget3] · [One-term estimate][consumer2]

`size_core` individually bounds the ten siblings and this term. `joint_core` inserts the actual estimate for $O$ and deduces
$$
\mathrm{ASK}-\mathrm{Ga}\le (2\log(4)C+13\,\mathrm{sg})U.
$$
Here $\mathrm{Ga}$ is the ledger gain. Ten of the eleven summands receive one $\mathrm{sg}\,U$ allowance each, and the remaining prime term receives $(2\log(4)C+3\,\mathrm{sg})U$. Keeping the other ten allocations fixed permits the upper coefficient $2\log(4)C+12\,\mathrm{sg}+4x^{-1+\varepsilon}$ already at the standard orbit cap. At $B=0$ the last addend can be removed. More generally for $0\le R\le Tx^{-2+\varepsilon}$ one can charge $4amR$ in its place before normalizing. These deductions change the bound applied at the omission step. The symbol `tOutD` in the source continues to denote its original numerical cap. The independent bound on $\sum_p\log(p)\,\mathrm{io}(p)$ uses its own incidence hypothesis. [Aggregation][consumer3] · [Insertion of actual omissions][consumer4] · [Separate incidence bound][consumer5]

## Why one full-scale term survives

For served primes below $X'$, the per-prime coefficient is $Q_1$ at $p<p_0$ and $Q_2$ otherwise. The sum bound permits $Q_2$ over the entire selected set below $X'$ and also adds the $Q_1$ small-prime charge, then applies a bound for the sum of prime logarithms. This explains the coefficient $2\log(4)X'Q_2$. It is a particularly coarse allowance if few primes enter the served set. [Definition of the two coefficients][class1] · [Bound on the two prime sums][primes1] · [Served-prime restriction][primes3]

With all scale hypotheses, `xprime_q_two_expand` gives the exact identity
$$X'Q_2=Cb+CX(\eta+S_c)+C(b/n)(\log x)w_8+CXt(\log x)w_8+Xb_o.$$
Here $X$ is the proof's positive auxiliary value for $X'$, and $w_8\ge1$ under the source's scale hypotheses. All four terms after $Cb$ are nonnegative. Multiplication by $2\log(4)mT$ thus gives a lower bound for the allocated coefficient,
$$2\log(4)CU\le\mathrm{tPrHigh}\le(2\log(4)C+3\,\mathrm{sg})U.$$
The upper bound is the named `size_prime_high_bound`. The original defines `SizePrHighLower` as a proposition. Searching the pinned source found only its definition under that name. The displayed lower inequality follows by signs from the expansion. For fixed $C>0$, $K$ and $0<\varepsilon<1/4$ along admissible scales with positive $U$ tending through $x\to\infty$, the normalized *allowance* tends to $2\log(4)C$. At $C=0$ the upper allowance is $3\,\mathrm{sg}\,U$. The accounting does not force a positive lower bound for the actual deficit and does not determine the value of $C$ for an individual selected host. [Window signs][window2] · [Budget definitions][window3] · [Lower-bound proposition][window4] · [Exact expansion][growth2] · [Named upper estimate][growth3]

## Which bound reaches the endpoint

`joint_core` weakens its two precise inequalities to $(3C+13)U$ and $U$ using $2\log4\le3$ and $\mathrm{sg}\le1$. `joint_discriminant_bound` selects the coarse pair by the projection `.2`. Its eventual version obtains a scale threshold for each allowed $\varepsilon,e,K$. The family consumer extracts $C$ and thresholds from assumptions, combines the applicable thresholds by taking their maximum, and passes on the family witness $3|K|+13$. The local improvement verified above is lost at this interface without a refined output statement and its propagation. [Coarse output and projection][consumer5] · [Extraction of constants][ties3] · [Transfer to family reads][ties4]

For the ordinary RH declaration and the right-half-plane Dirichlet declaration one can trace the following source-body references through the global construction, in the calling direction. A line that merely imports a module would establish weaker evidence.

| Calling body | Argument or call used |
|---|---|
| `riemannHypothesis`, `LFunction_ne_zero_of_half_lt_re` | `rhOfAll`, `allChi`, then `UpperTheory.FinalTheorems.everyCharacter`. [Endpoints][end1] · [Kernel wrapper][kernel1] |
| `everyCharacter` | `everyCharacter_of_row` calls `every_character_of_literature_of_vWin`. [Final character declaration][main1] |
| Literature and theta assembly | `every_character_of_theta_integrals_local_matching` passes to `every_character_of_green_v_win`. [Literature call][lit1] · [Theta assembly][theta1] |
| Green-function and window construction | `zero_free_all_of_green_v_win` passes `shape_closed_link_n_of_green`; this obtains `link_gl` and passes its second projection. [TopPlug][plug1] · [Obtaining the global link][shape1] · [Using both projections][shape2] |
| Global link | `link_gl` uses `FamGLmin.link8`, whose body calls `link7`, which calls `linkGLOBAL7_min`. [Global interpolation][gl1] · [Family calls][link1] |
| Concrete global construction | `linkGLOBAL7_min` calls `linkGLOBAL7_items`. The latter supplies `lossF_of_7` applied to `Loss7.stLoss7` to `linkCore`. [Proof bodies][min2] |
| Small-share estimates | `stLoss7` calls `losses_of_small_share_weight`, which uses `joint_discriminant_eventually`. [Wrapper][ties5] · [Eventual call][ties3] |

This is one route in a multi-input proof. It records visible theorem arguments, not a computed closure of elaborated proof terms. The older unnormalized `tops_clause` has a separate actual consumer in `loss_points_of_choices`. That theorem flows into `stCore`, `stLoss`, then `slope_loss_lemma_family`, with explicit uses in the packet and older global constructions. Import reachability alone cannot show that this second route is indispensable to the headline or that the two parameter contracts are interchangeable. [Older contract][chosen1] · [Older estimate][oldtop1] · [Direct caller][old3] · [Core wrappers][old4] · [Slope loss][old5] · [Packet caller][oldfamily1] · [Older global caller][min3]

## Independent comparison with the pointwise prime-deficit budget

The separate `PointsLemma` construction is useful because the bad count occurs with a *different* coefficient, $3ma$. Its source defines `BTT` and the normalized `adm2` inequality. The proof instantiates its bad-count function on the retained set, and uses an inclusion to control omissions. For primes $p\le X''$ the pointwise estimate `low_le` charges a sum of eight terms; $p>X''$ is handled by `sum_high`. This division at $X''$ differs from the $p_0$ cut used in `tPrHigh`. [Point statement][points1] · [BTT and adm2][points2] · [Pointwise formula][lossE1] · [Instantiation][ledger4]

Writing shares of $U=mT(a/x)$ in order, the eight upper allowances are $1/20,1/40,3/2,1/40,1/40,3,1/40,1/30$. The seventh is the weighted bad count. The third charges a prime logarithm sum below $X'$. The sixth charges the $A_4$ prime set at weight $\log(p)/p$. The high range receives a further $1/40$. The eight shares sum to $281/60$, which the source rounds to $47/10$. Adding the high allowance to the unrounded sum gives $113/24$, which fits beneath the stated $5$. Removing only the seventh upper allowance gives $559/120$ for the low sum and $281/60$ after adding the high term. These are sums of independently permitted upper bounds; the proof supplies no simultaneous saturation example. The pointwise incidence branch is handled separately. The exact comparisons here establish what can be recovered *within this ledger*. The explicit endpoint chain above identifies the distinct discriminant ledger. [Eight bounds and high range][ledger3] · [Third and sixth prime sums][ledger2] · [Aggregation and incidence][ledger5]

## Which upstream prime support can change the leading allowance?

Write $N=|TT|>0$. For the concrete family, take $S$ to consist of primes in the ledger prime set that are served, have host class `inertClass`, and satisfy $p_0\le p<X'$. The local record uses `loG` and the actual served subsets $TT_p$. Its prime charge already vanishes for the other host classes, although the ledger prime universe can also contain signal primes. The upper-bound proof first enlarges the prime expression to `loF` and then enlarges the top multiplicity from $|TT_p|$ to $N$. [Concrete local record][ld1] · [Prime classes][localp1] · [Actual per-prime envelope][localp2] · [Concrete comparison][old7] · [Class gate and its relaxation][old8] · [Cardinality enlargement][primes4]

Let $\Theta_S=\sum_{p\in S}\log p$ and $\Theta_{\mathrm{eff}}=\sum_{p\in S}(|TT_p|/N)\log p$. At the earlier per-prime envelope, with local coefficient $C\ge0$, the contribution from its individual summand $Cb'/x$ over this support is $2C U\Theta_{\mathrm{eff}}/X'$. This uses $X'b'=xb$ and $U=mNb$. This expression is one component of a bounding formula. Computing it for the original witness requires its concrete scale, classes and served subsets. [Scale identity][scale1] · [Weighted local envelope][primes4]

The source premises also bound what can be gained by retaining the multiplicities at a *fixed* support. Since $TT_p\subseteq TT$, the cardinality shortfall is exactly $|TT\setminus TT_p|$. Missing tops at a served prime belong to its counted bad set, and a served prime outside the eligible set has no omissions. With $p<X'$ and $\log p\ge0$ one obtains
$$
0\ \le\ \frac{\Theta_S-\Theta_{\mathrm{eff}}}{X'}
=\frac1N\sum_{p\in S}\frac{\log p}{X'}|TT\setminus TT_p|
\ \le\ \frac1N\sum_{p\in S}\frac{\log p}{p}|TT\setminus TT_p|
\ \le\ \frac BN\ \le\ x^{-2+\varepsilon}.
$$
The second inequality uses the **unscaled** subset/weighted comparison; no division by $ma$ is required. Thus, even away from the all-good face, restoring the exact number of served tops changes this normalized prime weight by at most $x^{-2+\varepsilon}$. At $B=0$ the two weights agree. For $m>0$ and fixed $C\ge0$, the difference of the two $Cb'/x$ allowances divided by $U$ is at most $2C x^{-2+\varepsilon}$. In particular, on scales tending to infinity with fixed $0<\varepsilon<1/4$, the difference tends to zero. This deduction isolates the remaining question: how large is the prime support $S$ itself on admissible families? A sparse support or an improvement of the underlying local upper bound could lower the charge. The available subtraction estimate alone does not decide the size of that support. [Set inclusion and positivity][consumer1] · [Concrete omission transfer][old6] · [Normalized bound][chosenp1]

[budget2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean#L36-L58
[budget3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean#L60-L84
[budget4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean#L86-L104
[chosen1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean#L23-L36
[chosenp1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/WeightVectorSmallSharesSeven.lean#L17-L18
[class1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/SecondKindBucket.lean#L151-L153
[consumer1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L29-L74
[consumer2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L114-L130
[consumer3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L145-L176
[consumer4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L178-L213
[consumer5]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L214-L241
[end1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L1-L12
[gl1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean#L14-L31
[growth2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L444-L462
[growth3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L515-L524
[harm1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ObjOnNarrowOfObjectsExist.lean#L98-L129
[harm2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ObjOnNarrowOfObjectsExist.lean#L130-L187
[host1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BadCharacterBound.lean#L17-L34
[host2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BadCharacterBound.lean#L36-L57
[kernel1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L7-L16
[ld1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/SuppSat.lean#L26-L70
[ledger2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L59-L85
[ledger3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L86-L121
[ledger4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L189-L226
[ledger5]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/LatticeChainSuccOfPartial.lean#L227-L251
[link1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/LogXLowerFamilyOfTheorems.lean#L60-L75
[lit1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L810-L813
[localp1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L97-L98
[localp2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalTheoremInputs.lean#L109-L124
[lossE1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/SecondConstantNonneg.lean#L85-L103
[main1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L7-L14
[min2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean#L720-L735
[min3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean#L763-L771
[old3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L2102-L2110
[old4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L2156-L2158
[old5]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L2205-L2210
[old6]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L722-L764
[old7]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L1114-L1122
[old8]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L1178-L1192
[oldfamily1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/GlobalReductionOfCompatibleFamily.lean#L144-L165
[oldtop1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean#L1772-L1790
[plug1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean#L12-L18
[points1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean#L37-L45
[points2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean#L90-L96
[primes1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L530-L551
[primes3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L891-L907
[primes4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L846-L878
[primew1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean#L357-L393
[primew2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean#L394-L433
[scale1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean#L87-L93
[shape1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L33-L35
[shape2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L51-L55
[theta1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L69-L73
[ties1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L16-L34
[ties2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L41-L80
[ties3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L86-L101
[ties4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L126-L161
[ties5]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L165-L167
[window2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L95-L115
[window3]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L130-L161
[window4]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L163-L187
