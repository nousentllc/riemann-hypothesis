# What the original selector can distinguish

Fix the principal conductor-one family, one of its raw arithmetic hosts, a sufficiently late scale $`x`$, the ordering of the labels on this particular host, and the Frobenius step for every prime. The cyclic group has dyadic order $`n\asymp x^{h}`$, $`h=2+8\varepsilon`$, and $`\delta=x^{-\varepsilon/8}`$. The original retained mask is existential. The following construction tests the logical strength of that selector on the same raw host. It gives no membership decision for its particular chosen mask.

The published conductor-one selector uses the uniform law with individual inclusion probability $`\delta`$. Its complete scalar comparison at the point of choosing $`T`$ can be written as
```math
 S(T)=\frac{(|T|-\delta n)^2}{2\delta n}+
      \frac{B(T)}{4M},\qquad
 M=C_bx^{-2}\delta n\sum_p\omega_p,\qquad \omega_p=(\log p)/p .
```
Here $`B(T)=\sum_p\omega_p\#\{\hbox{retained points on bad orbits at }p\}`$ uses precisely the source-eligible primes. The intermediate choice has positive uniform-law probability and $`S(T)\le\mathbb E_{\mathrm{uniform}}S`$. In particular $`\mathbb E_{\mathrm{uniform}} S\ge(1-\delta)/2`$ by the binomial count variance. The exported size, coset shares and bad-mass bounds are weaker.
[Selection score and existential witness](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173) · [Default profile and count variance normalization](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean#L90-L125) · [Final retained-set contract](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/topsBase.lean#L79-L97).

## The fixed-cardinality model

Orient the root parity classes by the source's least numeric label. Call the root-even half $`E`$, and the root-odd half $`B`$. Of $`B`$'s two children modulo four, let $`b,c`$ be their least actual host labels, listed so $`b`$ is the least label in $`B`$. Residues below refer to the additive cyclic coordinate of these elements. In $`B`$ allow only their two congruence classes modulo 16. Denote these two strata by $`S_b,S_c`$, each of size $`n/16`$. All of $`E`$, of size $`n/2`$, is the third allowed stratum. Each allowed residue follows its canonical even child at both levels below its modulo-four parent. This uses the minimum of the actual coset rather than a numerical coincidence of coordinate and label. [Canonical base definition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L264-L275).

Take $`N`$ nearest to $`\delta n`$. Choose $`k_b=k_c`$ nearest to $`\delta n/8`$, and choose $`k_E=N-2k_b`$. Sample uniformly without replacement in each stratum with those fixed counts; the three samples are independent. The rates are asymptotically $`2\delta`$ in the leaves and $`3\delta/2`$ in the reservoir. Every realization has positive probability under the original uniform Bernoulli law. Its first source score term tends to zero. Establishing that some such realization also clears the actual bad-mass test requires the following rare-event estimates.

## Why the bad-mass constant stays the same

Write $`\mathrm{val}_2(s)`$ for the dyadic valuation of a nonzero step $`s`$ and $`L`$ for its orbit length. In a cell of $`u=\lceil1/\delta\rceil`$ consecutive orbit positions, the table lists the limits of the sum of inclusion probabilities over all sites and over the even sites. Only occupied orbits occur. The error is uniform since every relevant supported pattern has period dividing 16 and fixing a count changes its stratum rate by $`O(1/n)`$.

| Orbit type | All sites | Even sites |
|---|---:|---:|
| Odd step, entire group | 1 | 3/4 |
| Even step in $`E`$ | 3/2 | 3/4 |
| In $`B`$, valuation 1 | 1/2 | 1/4 |
| In $`B`$, valuation 2 | 1/2 | 1/2 |
| In $`B`$, valuation 3 | 1 | 1 |
| In $`B`$, valuation at least 4 | 2 | 1 |

Under independent inclusion at the stratum rates, the probability of an empty cell tends to $`e^{-\mu}`$, and that of a singleton at an even position tends to $`\mu_e e^{-\mu}`$. Both limits are at least $`e^{-2}>0.13`$ in the table. Fix a uniform bound of 0.12 eventually. A trial tile of $`6r+1`$ disjoint cells therefore meets the original mark condition with probability at least $`0.12^{6r+1}`$. This argument treats zero-rate sites explicitly. The published bound requiring every site rate to exceed $`3\delta/4`$ does not itself apply. [Marks and three orbit conditions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26).

For a fixed retained anchor $`t`$, conditioning within its stratum leaves a uniform sample of $`k-1`$ among $`m_0-1`$ points. For any $`m`$ inspected points in a remaining population of $`M_0`$, with sample size $`K_0`$, a prescribed pattern with $`i`$ successes has probability
```math
 (K_0)_i(M_0-K_0)_{m-i}/(M_0)_m .
```
Here $`(a)_i`$ is a falling factorial. Relative to independent trials with the conditional marginal $`K_0/M_0`$, this probability is at most $`M_0^m/(M_0)_m`$. The claim also holds when both probabilities vanish. Multiplying over three strata and summing over the event's patterns bounds each event probability by $`1+o(1)`$ times its product-law probability, uniformly for $`m=O(\delta^{-1}\log x)`$, since $`m^2/(n/16-1)=o(1)`$. The relative bound preserves very small probabilities. The conditional marginal differs from its unconditional value by $`O(1/n)`$.

* **Sparse short windows.** Let $`K=\lceil8(h+2)/\varepsilon\rceil`$, and $`L_2`$ be bounded by the fixed source constants. At most $`L_2`$ windows contain the anchor. A violation there requires $`K`$ other retained points. At other windows it requires $`K+1`$ retained points. All marginals are at most $`2.1\delta`$ eventually, so the conditional failure probability is $`O(L_2 {L_2\choose K}(2.1\delta)^K + L {L_2\choose K+1}(2.1\delta)^{K+1})=o(x^{-2})`$. The extra point at starts away from the anchor matters when $`\varepsilon K/8=h+2`$ exactly.
* **Marked tiles.** Each block of $`M_*+1`$ consecutive trial tiles has at least $`M_*`$ distinct, disjoint tiles after omitting any tile containing $`t`$. The source ensures sufficient orbit length for every eligible prime. Disjoint tiles are independent under the comparison law. Inspection uses $`O(\delta^{-1}\log x)`$ points. Union over starting tiles gives $`O(L\exp(-M_*0.12^{6r+1}))=o(x^{-2})`$, since $`M_*\ge(h+3)\log(x)10^{6r+1}`$.
* **Long windows.** With $`k=N_1-1`$, the published threshold has $`k\ge6eG'\delta`$ and $`k\ge(h+3)\log_2 x`$. After conditioning on $`t`$, a violation requires at least $`k`$ retained unconditioned points. The elementary union over $`k`$-subsets bounds each comparison probability by $`(eG'2.1\delta/k)^k\le0.35^k`$ (zero if $`k>G'`$). Multiplying by the comparison factor and at most $`L=O(x^h)`$ starts gives $`o(x^{-2})`$.

These arguments use the literal windows in the pinned source. In particular, $`\log x`$, $`r`$, $`K`$ and $`\varepsilon`$ are held in the same eventual order as in the published proof. [Source scales and $`K`$](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/MarkedLow.lean#L20-L31) · [Tile lengths and long-window cap](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L237-L252) · [Size of an eligible orbit and constants](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/orbitTerms.lean#L107-L136) · [Removing the tile containing the anchor](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/TilesLe.lean#L43-L67).

Multiplying by the marginal of each retained anchor and summing against the original nonnegative weights gives $`\mathbb E B=o(x^{-2}\delta n\sum_p\omega_p)`$. The estimate applies to any fixed positive original $`C_b`$. Markov's inequality gives $`B/M=o(1)`$ on a set of probability tending to one (take a threshold tending to zero slower than its expectation). If $`\sum_p\omega_p=0`$, then $`B=0`$ identically. All such masks clear the original comparison to its *uniform-law* mean. They also satisfy its exact cardinality scale and all exported obligations. The construction never claims to evaluate the original choice function.

## Geometry of recovery on a late host

For valuation-one steps in $`B`$, write $`s=2s'`$, with $`s'`$ odd. Divide cyclic coordinates within $`B`$ by two, after translating to its even child base. The two supported classes on the resulting order-eight quotient have odd difference $`d'=(c-b)/2\bmod8`$. If $`s'\equiv\pm3d'\bmod8`$, neither type of directed successor edge is possible on this orbit. There are exactly $`n/8`$ such steps. The $`n/8`$ figure counts all group steps, including the other valuations in the denominator. Each of these orbits has length $`n/2`$, retained count $`2k_b`$, and odd count $`k_c=N/8+o(N)`$. The previous host-uniform prime-step comparison therefore gives joint-sign prime log-weight $`H/32+o(H)`$ for these directions. Removing the upper/lower strips in the bulk, dropped primes and unserved tops costs $`o(HN)`$ in log-weighted top incidences. [Step-weight and omission arguments](https://github.com/nousentllc/riemann-hypothesis/pull/10).

For each active orbit and lift put $`A=g_U-\mathrm{Pr}, F=(g_0)_+`$. Then $`F-A=\mathrm{Pr}-C+(-g_0)_+`$, where $`C`$ is the sum of excluded excesses and even-source minima, and $`(-g_0)_+\le dl`$. On the blocked orbits the exponent-one excluded excess vanishes, and all even-source first minima use thin fill. One geometric tail bounds deep credit by $`O(N_v a/p^3)`$. On the prime interior $`p\ge H/x`$, this gives $`C=o(N_v\lambda)`$ uniformly. The variable price is $`O_v\lambda+o(N_v\lambda)`$, where $`O_v`$ is odd count. The fixed price and $`dl`$ summed across active orbits at each prime cost $`o(N\lambda)`$. Indeed their length-dependent parts sum to
```math
 O\!\left(\lambda+n(\eta+c_G+Nm)+n\,Nm^2\log_2(2a)
                +N\log_2^2(2a)\right)=o(N\lambda)
```
on the source windows. Actions by different lifts are controlled uniformly. Hence these singular directions contribute exactly $`2\,(1/32)(1/8)+o(1)=1/128+o(1)`$ to the normalized fallback recovery $`\mathcal R_x`$. All other contributions are nonnegative. [Source gain and floor](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L234-L268) · [Local identity and transport to actual recovery](https://github.com/nousentllc/riemann-hypothesis/pull/11).

### Reachability of the exact $`1/128`$ value

It is possible to make the remaining recovery $`o(1)`$ with the same selected mask. For every eligible directed orientation present on a long orbit, there are at least $`L/16`$ disjoint geometrically permitted pairs of that orientation. This follows from period 16. Odd steps have both orientations on the full group, since every allowed point of $`B`$ has its neighbors in $`E`$. Even steps in the reservoir have both orientations. Valuation one in $`B`$ has both orientations absent in the two blocked classes above and exactly one orientation present for each of the other two. At valuations two and three all supported positions in $`B`$ are even. At higher valuations every position in an occupied $`B`$-coset is eligible.

First use independent trials with the exact stratum marginal probabilities. Pair indicators for a fixed orientation are independent since the underlying edges are disjoint. The expected success count is $`\ge cL\delta^2`$ with uniform $`c>0`$. A lower-tail exponential bound, then a union bound over at most $`2n^2`$ oriented step/orbit choices of length $`L\ge\sqrt x`$, makes the probability of any orientation falling below $`cL\delta^2/2`$ at most $`2n^2\exp(-c'\sqrt{x}\delta^2)`$. Conditioning on the three fixed counts costs at most $`(n+1)^3`$: each chosen count is a mode of a binomial variable with its mean equal to that integer and thus has probability at least $`1/(n+1)`$. The good matching event therefore holds with probability tending to one in the fixed-size model. This is an intersection with the original score event already established.

An even-to-odd first hit pays full adjusted supply, $`\ge b'/2`$ eventually. A reverse-only first hit pays the positive excess. On $`H/x\le p\le H/(1+x^{-1/2})`$, that excess is at least $`b'/(2\sqrt{x})`$ eventually. Indeed $`(a_s-2c_G)/p`$ exceeds $`b'(1+x^{-1/2})(1-2c_G/a)`$, while the capped target is at most $`b'(1+\beta)+\lambda+\eta+c_G`$, with $`\beta=O(x^{-2})`$. Since $`\sqrt{x}\delta^2\to\infty`$, even the smaller credit dominates $`L\lambda`$. The price is at most $`L\lambda(1+o(1))`$ and $`dl=o(L\lambda)`$, uniformly. Hence any such long orbit with a realized orientation has $`A>F`$. Orbits with zero odd occupancy cost at most the already accounted fixed price plus $`dl`$ in recovery. Short-order directions have total log-weight $`o(H)`$ under the pointwise prime-step theorem. The remaining upper strip costs $`O((x^{-1/2}+1/H)\log H)=o(1)`$ of the normalized recovery, by the bound $`(F-A)_+\le O_v(\lambda+\eta)+\text{fixed price}+dl`$. Thus $`\mathcal R_x\to1/128`$ for compatible buffered choices.

## The local charge and final gap on those same choices

The predecessor study yields $`\mathcal K_x=(2N)^{-1}\sum_{t\in T}w(t)+o(1)`$, where $`w`$ averages odd positions across all step directions. At dyadic level $`j`$, the step mass is $`2^{-j-1}`$. In $`E`$, the root bit is zero and lower bits are fair under uniform sampling in $`E`$, so the mean score is $`1/4-1/(2n)`$. In the two buffered leaves, the root bit is one, the next bit is balanced across leaves, the next two bits are zero, and the remaining bits are fair within each leaf. Their combined mean is $`21/32-1/(2n)`$. These masses are unaffected by a permutation of numeric labels. Sampling without replacement in each stratum gives variance $`O(N)`$ for the sum of the bounded scores. Intersect its concentration (for example within $`N^{3/4}`$) with the two high-probability events above. Since $`k_E/N\to3/4`$ and $`(k_b+k_c)/N\to1/4`$, the local charge tends to
```math
 \tfrac12\bigl((3/4)(1/4)+(1/4)(21/32)\bigr)=45/256.
```
On these compatible witnesses, the signed gap therefore tends to $`45/256-1/128=43/256`$ and the fraction of the nominal local charge recovered tends to $`2/45`$. This limit invokes the family transport from the preceding study. These arithmetic deductions are written analyses; this package's numerical tests and any Lean receipts have narrower scopes.

### A zero-recovery comparison with the same inner score

For completeness take one uniform fixed-size stratum containing the entire host, with the same nearest-integer count. The probability arguments above simplify. Independent cell means tend to 1 and 1/2 for all and even sites, so empty and even-singleton probabilities exceed 0.12 eventually. The anchor-sensitive short-window estimate again gives the strict improvement to a vanishing multiple of the original bad-mass budget. Conditioning on one modal total count suffices for simultaneous edge abundance. Thus this witness also has original score tending to zero. On every long orbit the even-to-odd edges suffice for strict specialized dominance. The remaining prime mass is negligible, and uniform dyadic exposure gives a limiting charge of 1/4. Consequently zero and positive limiting recovery are both compatible even with the original private comparison to its uniform-product mean.

## Finite checks

The [initial design](DESIGN.md) and [buffered design](BUFFERED_DESIGN.md) identify which claims were registered before each finite panel. Under the initial two-class control, 40,320 quotient labellings produced 483,840 supported orbit checks with no density discrepancy. Every ordering had exactly two blocked odd directions and one with only a reverse edge. The finite cell threshold of 1/10 held at all ten tested widths. At width 16 the least empty probability was 0.105273, below the more demanding 0.11 threshold. The deliberately misoriented support $`\{0,3\}`$ has a supported orbit at step 2 with no even position available for a mark. This initial control by itself does not satisfy the private centered size test.

In the buffered panel, all 54 label/size instances gave the source-exposure expression $`45/256-1/(4n)`$ before integer rounding, and a normalized blocked contribution of $`1/128`$ at the level of the orientation and rate weights. The 5,080 anchored/unanchored sample-pattern comparisons agreed with the falling-factorial law and its relative upper bound. Neither panel simulates how the kernel chooses an existential set. [Initial exact checks](results.json) · [Buffered checks](buffered-results.json).

From this directory, run the following using Python 3.11 or newer.

~~~sh
python3 -B geometry.py --check
python3 -B buffered.py --check
~~~
