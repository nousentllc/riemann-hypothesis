# The actual signed deficit and the fallback gain

Fix one sufficiently large selected family point, its selected integer weights, tops, dropped primes, active representatives and source constants. Write $`H=X'`$, $`B=b'=a/H`$, $`\lambda=B/x=b/H`$, $`N=|TT|>0`$, $`m=|J|>0`$, $`U=mNb`$, and $`\Delta=\mathrm{ASK}-\mathrm{Ga}`$. In the following $`e`$ is a positive exponent in a prime power and $`\eta`$ is the recorded size tolerance. The finite statements and asymptotic derivations use the original source at commit 40e56bab. The kernel receipt below covers the scalar comparison rules.

## What the prime ledger actually adds

At a served central prime on an active orbit $`v`$, let $`Q_{jv}`$ be the sum of actual demand over its retained tops for lift $`j`$. It is precisely the sum of **askP**. The finite definition involving the numbers $`wPart`$ agrees term by term with askP on the filled record, and its tails vanish. The auxiliary askG supplies an upper comparison elsewhere in the proof. [Actual ask equality](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L223-L245) · [Rational-prime ask equality](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L298-L310) · [Global demand equality, including the ramified term](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L362-L398).

With $`A_{jv}=g_U-{\rm Pr}`$, $`F_{jv}=\max(g_0,0)`$, $`T_v=\lceil t_v\rceil_++D_p+1`$, the actual gain is $`\max(A_{jv},F_{jv})`$. The orbit's contribution **after** its share of the tax is exactly
```math
 Q_{jv}+T_v-\max(A_{jv},F_{jv})=
 \min(Q_{jv}+T_v-A_{jv},Q_{jv}+T_v-F_{jv}).
```
Thus the recovery relative to always using $`A`$ is $`(F_{jv}-A_{jv})_+`$. At an active prime an additional $`{\rm ep}_p`$ is charged once across all orbits and lifts. Representatives outside the active set supply $`F_{jv}`$ to gain, and their tops still contribute full demand. The term $`T_v`$ is charged once per lift, including when the fallback wins. A choice of one winning branch for all lifts would change this identity. For instance, $`A=(6,0)`$, $`F=(0,6)`$ gives selected gain 12, whereas either uniform choice gives 6. [Source branch, tax, reverse advantage and fallback definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L336-L366) · [Decomposition by active and complementary orbits](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean#L679-L728).

The rational-prime gap weights the signed local deficits by $`2\log p`$. At dropped primes the gain in the actual record is zero. Demand and tax there are nonnegative. The extra ramified demand has coefficient $`\log d`$ times a sum of positive parts, hence is nonnegative. The separate incidence variable uses the opposite branch difference,
```math
 {\rm Sv}_v=\left\lceil \sum_j(A_{jv}-F_{jv})_+\right\rceil,\qquad
 {\rm io}_p=2\,{\rm Sig}_p\max_{v\ {\rm active}}{\rm Sv}_v,
```
with zero incidence for an empty active set. It does not appear in $`\Delta`$. Even when incidence is counted separately, the selected signal budget gives $`\sum_p(\log p){\rm io}_p\le a mN x^{-9}=Ux^{-8}`$. Here the prime weight has no leading factor two. Increasing $`F`$ at fixed $`A,\mathrm{Sig}`$ can only decrease this incidence cost. [Deficit and prime weights](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/SecondKindBucket.lean#L13-L26) · [Gain and incidence transports](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean#L186-L275) · [Selected signal bound](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean#L42-L76) · [Unrounded incidence budget](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L96-L110).

## A positive lower bound in a winning orbit

Let $`N_v`$ be its number of retained tops, $`O_v`$ its number of odd retained tops, and $`J_v`$ its number of directed complementary-parity adjacencies from a selected even position to its selected odd successor. Put $`V_v=O_v-J_v`$. All three counts use the same oriented cycle and representative as $`g_U`$. The following argument applies on a served, active, central high prime, $`p_0\le p<H`$.

1. For all lifts $`j`$, $`0\le\kappa_j\le\mathrm{Sc}\le c_G`$. Thus $`{\rm capU}={\rm fill}-\kappa_j+c_G\ge{\rm fill}`$ and $`{\rm al}=a_s-2c_G\le a_s`$. Omitting nonnegative excluded terms and subtracting $`dl\ge0`$ gives $`F_{jv}\le Q_{jv}`$. On odd sources the $`g_U`$ terms reduce, via the odd geometric series, to positive parts with the same shifted height and cap. On even sources the positive-part-plus-minimum identity gives
   ```math
   g_U\le Q_{jv}+ M_{jv},\qquad
   M_{jv}=\sum_{s\ {\rm even\ selected}}\sum_{e\ {\rm odd}}
        \min(a_s/p^e,{\rm fill}_{j,s+e h_p}).
   
```
   This is the upper direction; the original lower-direction inequality is used for the other side. [Actual gain definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L228-L267) · [Lift and error bounds](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L52-L88) · [Positive-parts identity](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L246-L269) · [Nonnegative floor loss and price](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean#L128-L205).
2. For an even source whose immediate successor $`y`$ is a selected odd top, the nearest-even distance of $`y`$ is one. Its contribution to $`M`$ at $`e=1`$ is $`\min(a_s/p,b_y+o_{jy})`$. The tax $`T_v`$ includes $`\min(a_s/p,b_y)`$ through $`t_v`$. The difference is at most its top offset $`o_{jy}`$. Other immediate successors of even sources are thin. Indeed the central partner has first component false, but the source definition of thick requires true. The sum of their fills is at most $`N_v(w''+\eta)`$. Every odd exponent $`e\ge3`$ contributes at most the geometric tail $`2a/[p^3(1-p^{-2})]\le4a/p^3`$ per even source. The remaining terms in $`t_v`$ and $`D_p+1`$ are nonnegative. [Partner and thin status](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L131-L151) · [Nearest-even tax](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L206-L225) · [Explicit case-E tax and ceiling argument](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L784-L828).
3. The high-central price contains $`\sum_{y\ {\rm odd}}(o_{jy}-\kappa_j)`$ plus a nonnegative term. Matched offsets pay the excess in step 2. Each of the $`V_v`$ other odd tops has $`o_{jy}\ge\lambda`$. It follows that
   ```math
   Q_{jv}+T_v-A_{jv}
       \ \ge\ \lambda V_v-E_{jvp},\qquad
   E_{jvp}=N_v(\kappa_j+w''+\eta+4a/p^3).
   
```
   The same lower bound applies to the actual orbit deficit on lifts with $`A_{jv}\ge F_{jv}`$. On the other lifts $`Q_{jv}+T_v-F_{jv}\ge0`$. Moreover $`a_s/p\ge a/H=B`$ and $`b_y\ge B`$, so each matched immediate edge costs at least $`B`$ in $`T_v`$. On *either* branch the actual deficit is therefore at least
   ```math
   \lambda\min(V_v,xJ_v)-E_{jvp}.
   
```
   In particular $`(x+1)J_v\ge O_v`$ suffices for the same $`\lambda V_v-E_{jvp}`$ floor regardless of the winning branch. This does not establish which branch actually won. [High-central price expansion](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L769-L785) · [Top height lower bounds](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L99-L103).

The fallback lower bound also includes every excluded $`e=1`$ demand $`(a_s/p-b_{s+h_p}-o_{j,s+h_p})_+`$ from a selected top to its distinct selected successor. These are absent from $`g_0`$ by its first-distance exclusion predicate. The bound $`xJ_v`$ used above only needs the tax on even-to-odd matches. [First-distance exclusion and fallback](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L234-L252).

### Strict branch selection on orbits with enough complete edges

Let $`L_v={\rm ord}(h_p)`$ be the **cycle length**, with $`N_v\le L_v\le n`$. Write $`\mathcal C_{jv}`$ for the sum of excluded positive-demand columns over all sources plus all minimum columns over even sources. The column partition gives $`A_{jv}-g_0=\mathcal C_{jv}-{\rm Pr}`$. Each of the $`J_v`$ complete even-to-odd edges supplies two pieces of its first column. The positive part is excluded because the successor is distinct and its distance one is the first visit. The minimum comes from the even source. Together they give its full shifted height $`(a_s-2c_G)/p\ge(a-2c_G)/H=B(1-2c_G/a)`$. The summands for different edges are distinct, and all other pieces of $`\mathcal C`$ are nonnegative. Also $`g_0\ge-dl`$. Therefore the finite sufficient inequality
```math
 J_v B(1-2c_G/a)>{\rm Pr}+dl
```
gives $`A_{jv}>\max(g_0,0)`$, including when the raw $`g_0`$ is negative. The common floor loss $`dl`$ cancels in the raw comparison; its appearance in this sufficient test also guarantees that $`A`$ beats zero. [Column expressions, exclusion and common loss](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L228-L267) · [Orbit length and retained count](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L690-L738) · [Raw branch difference](../local/ActualGain.lean).

Uniformly in the high band and in all lifts, with $`z=\log_2(2a)`$, the exact source formulas imply
```math
 \frac{{\rm Pr}}{L_v\lambda}\le
 \frac{O_v}{L_v}(1+\eta/\lambda)
 +K_{\rm Pr1}\big[1/n+(\eta+c_G+N_m)/\lambda\big],\qquad
 \frac{dl}{L_v\lambda}\le
 \big[K_{\rm dl1}N_m^2 z+K_{\rm dl2}z^2\big]/\lambda .
```
Here $`N_m=D.R.N(m)`$, $`c_G=4\mathrm{Sc}`$, $`w''=\lambda/n`$, $`z=O(x^\epsilon+\log x)`$, and $`K_{\rm Pr1},K_{\rm dl1},K_{\rm dl2}`$ are the fixed nonnegative coefficients of this family. The size window gives $`N_m\le x^{e_0}`$ for a fixed window exponent $`e_0`$, and $`\mathrm{Sc},\eta\le\exp(x^{\epsilon/4})`$. Since $`\lambda=\exp(x^\epsilon-x^{\epsilon/3})`$, the second ratio tends to zero and the first is at most $`O_v/L_v+o(1)`$. Also $`2c_G/a=o(1)`$. It follows that $`xJ_v/L_v\to\infty`$ uniformly on any specified collection is sufficient for strict choice of the specialized branch throughout that collection, eventually. This criterion applies to a selection with the proved edge abundance, and by itself gives no abundance result for the incumbent witness. [Exact high-range price](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L769-L780) · [Frame parameters and coefficients](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L31-L50) · [Size window](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L65-L117) · [Parameter identification on the record](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/SuppSat.lean#L66-L103).

## Contributions outside the interior

In the family limit $`p_0`$ is polynomial in $`x`$, while $`H=\exp(x^{\epsilon/3})`$. For every active central $`p<\sqrt H`$, all partners have first component false and are top or thin. From the family height window their fills are at most
```math
 F_{\max}=\max\{B(1+\beta)+\lambda+\eta,\ w''+\eta\}.
```
Let $`K_0=\lceil\log_2(2a)\rceil`$. For a single even source the terms through $`K_0`$ in $`M`$ cost at most $`K_0F_{\max}`$, and the sum after that is at most $`2a\,2^{-K_0}\le1`$. Since $`{\rm Pr}\ge0`$, both choices of gain are bounded by $`Q_{jv}+N_v(K_0F_{\max}+1)`$. Therefore these small primes can lower $`\Delta/U`$ by at most $`2\log(4)\sqrt H(K_0F_{\max}+1)/b=o(1)`$. Here $`F_{\max}=O(B)`$, $`K_0=O(\log a)`$, and $`B/b=x/H`$. This bound includes case D. [Nonnegative price on both ranges](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean#L185-L215) · [Family top-height cap](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/FamCore.lean#L122-L130) · [Finite log-sum bound](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L155-L162).

For $`p\ge\sqrt H`$, the error $`E_{jvp}/(N_v\lambda)`$ is bounded by
```math
 (\mathrm{Sc}+\eta)/\lambda+1/n+4x/\sqrt H=o(1).
```
All retained orbits together have at most $`N`$ tops per prime. The Chebyshev bound $`\sum_{p\le H}\log p\le H\log 4`$ makes the sum of these errors $`o(U)`$. Source window bounds give $`\eta,\mathrm{Sc}\le\exp(x^{\epsilon/4})`$, $`\lambda=b/H`$, and $`n\to\infty`$. At inactive central or signal primes the fallback alone gives a nonnegative deficit, as does the zero-gain branch. The same holds for dropped primes. These facts already imply $`\liminf\Delta/U\ge0`$. [Selected scale windows](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L65-L117) · [Inactive and active branch split](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean#L633-L685).

## Identity for the original selected witness

Let $`I_x`$ be the served active central primes in the high range
```math
 H/x\le p\le H/(1+2/x+\beta).
```
Write $`\mathcal K_x=(2/U)\sum_{p\ {\rm served\ high}}\log p\sum_{v,j}(D_{jvp})_+`$, the previous study's positive local charge including the unused even-source columns. On the given windows,
```math
 \boxed{\frac{\Delta}{U}
   +\frac{2}{U}\sum_{p\in I_x}\log p\sum_{v\ {\rm active},j}
          (F_{jv}-A_{jv})_+
   =\mathcal K_x+o(1).}
```

For the upper side, form a comparison sum by adding that displayed recovery back to the actual signed deficit. This replaces the maximized gain by $`A_{jv}`$ only on the specified active interior orbits, with their complementary fallback, $`{\rm ep}`$, tax, classifications and actual demands retained. The proof of the upper bound for $`\mathcal K_x`$ already compares against $`A_{jv}`$ there. It uses the true maximum elsewhere. Its residuals remain $`o(U)`$. For the lower side, use the unconditional specialized lower bound on each interior orbit in this comparison sum. Use the branch-independent lower floor in the rest of $`p\ge\sqrt H`$ and the preceding small-prime estimate below $`\sqrt H`$. The omitted prime weight below $`H/x`$ or in the upper strip is $`o(H)`$, since counting all integers gives normalized cost $`O((x^{-1}+\beta+1/H)\log H)=o(1)`$. Uniformly on $`I_x`$, $`(D_{jvp})_+=\lambda V_v+o(N_v\lambda)`$ by the predecessor calculation and the unused even-source bounds. At all primes this positive charge is at most $`N_v(\lambda+\eta)`$. The two sides now agree up to $`o(U)`$.

This comparison is arithmetic on the original record. It requires no new admissibility theorem for altered gains and no sign assumption on $`A`$. The equality identifies the one aggregate recovery that would have to be measured to evaluate the original witness gap. Vanishing of that recovery at an arbitrary selected witness has not been derived. If the matched-edge criterion fails on only $`o(H)`$ log-weighted top mass after division by $`N`$, the branch-free lower bound above and the upper bound give $`\Delta/U=\mathcal K_x+o(1)`$ for that more tightly described family. Exceptional mass here is weighted by each orbit's top count, rather than by its number of representatives. [Original active-orbit inequality, before the gain maximum](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L825-L849) · [Insertion of the gain maximum in the published summation](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean#L691-L728) · [Global upper residuals](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/DiscriminantSettingSatisfied.lean#L162-L220) · [Previous positive-charge definition and asymptotic comparison](https://github.com/nousentllc/riemann-hypothesis/pull/10).

## Verification scope

[GainGapTransport.lean](GainGapTransport.lean) proves the ordered-real branch identity, fallback recovery, matched-edge payment, specialized lower bound, winner-dependent lower bound, and branch-independent lower bound from their scalar inputs. Run the following with the supplied toolchain version and pinned Mathlib checkout. The [replay receipt](kernel.json) records the version, declared axioms and content hashes. The source-dependent estimates and the end-to-end limit in this note have not been independently kernel-replayed.

    python3 replay.py --toolchain /path/to/lean-4.33.1 --mathlib /path/to/pinned-mathlib
