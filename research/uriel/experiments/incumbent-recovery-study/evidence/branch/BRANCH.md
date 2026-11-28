# What the fallback recovers at missing shifts

Fix the original retained set $`T`$, one sufficiently late member of the family, a served central prime $`p`$, one active orbit and an admissible lift. Write $`N_v`$ for the number of retained points on the orbit, $`O_v`$ for its count at odd positions, and $`L_v`$ for its length. Use $`H=X'`$, $`b'=a/H`$, $`\lambda=b'/x=b/H`$, $`N=|T|`$ and $`U=mNb`$. The comparison in this note uses the actual signed gains from the source. [Original source expressions for the gains and price](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L230-L268) · [Original orbit maximum and tax](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L335-L362).

Put $`B=\sum_{\rm kept}d_{se}`$, $`C=\sum_{\rm excluded}d_{se}+\sum_{s\ {\rm even},e\ {\rm odd}}m_{se}`$, with $`u_{se}=(a_s-2c_G)/p^e,\ d=(u-\mathrm{capU})_+`$ and $`m=\min(u,\mathrm{capU})`$. The preceding source-linked supplement gives $`g_0=B-dl`$ and $`g_U-\mathrm{Pr}=g_0+C-\mathrm{Pr}`$. The recovery by the alternative is
```math
 R_{vjp}=\big[(g_0)_+-(g_U-\mathrm{Pr})\big]_+
         =\big[\mathrm{Pr}-C+(dl-B)_+\big]_+.
```
Both branches pay the same orbit tax, so it cancels in this difference. The separate incidence cost takes the opposite positive part. In particular $`R_{vjp}\ge \mathrm{Pr}-C`$, even if the zero floor is active. [Previous formal gain identity](https://github.com/nousentllc/riemann-hypothesis/blob/3dedd2d81a54d046e3c12ef78df9d9fd0c2ad6dc/research/uriel/experiments/actual-gain-study/evidence/local/ActualGain.lean#L58-L90).

## The necessary geometric hypothesis

Assume **all retained immediate successors are absent**, meaning $`s+h_p\notin T`$ for every retained $`s`$ on this orbit. This excludes both even-to-odd and odd-to-even edges. Knowing merely that the even-to-odd count vanishes would still permit large odd-to-even first-hit demand. On the high interior $`H/x\le p\le H/(1+2/x+\beta)`$, we have $`p^3\ge2H`$ eventually. The first excluded demands vanish by the hypothesis, and all deeper excluded demands vanish because $`(a_s-2c_G)/p^3\le b'`$ while any excluded target has cap at least $`b'`$. The immediate successor has first component false and is thin. Hence the first minimum on each even source is at most $`w''+\eta+c_G`$, and the entire later odd supply is at most $`2a/[p(p^2-1)]`$. This proves
```math
 0\le C\le (N_v-O_v)\left(w''+\eta+c_G+\frac{2a}{p(p^2-1)}\right)
           =o(N_v\lambda)
```
uniformly on the interior. Here $`w''=\lambda/n`$, $`n\to\infty`$, $`(\eta+c_G)/\lambda=o(1)`$, and $`a/(p^3\lambda)=xH/p^3=o(1)`$. [Central partner and thin offset](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L131-L160) · [Retained heights and lift bounds](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L226-L251).

The price includes all odd offsets minus lift corrections, plus a nonnegative fixed orbit price:
```math
 \mathrm{Pr}=\sum_{s\ {\rm odd}}(o_{sj}-\kappa_j)+
    K_{\mathrm{Pr}}L_v(w''+\eta+c_G+Nm),\qquad
 \lambda\le o_{sj}\le\lambda+\eta.
```
If $`N_v/N`$ stays bounded below then $`L_v/N_v=O(1/\delta)`$, and $`K_{\rm Pr}`$ is fixed throughout the family. The full fixed price is $`o(N_v\lambda)`$ because $`1/(\delta n)=o(1)`$ and the other errors divided by $`\lambda`$ vanish faster than any power of $`x`$. The common $`dl`$ is similarly $`o(N_v\lambda)`$ from its displayed polynomial-rank and logarithmic bound. More directly, each retained source contributes at least $`(a-2c_G)/H-(w''+\eta+c_G)`$ to $`B`$ at exponent one. Thus $`g_0>0`$ eventually. Provided $`O_v/N_v`$ also stays bounded below, $`\mathrm{Pr}>C`$, $`g_0`$ strictly wins, and
```math
              R_{vjp}=\mathrm{Pr}-C=O_v\lambda+o(N_v\lambda).
```
The recovered number has leading coefficient one per odd retained position. This result follows directly on **any supplied fixed witness** satisfying the hypotheses. [Source price on the high range](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L769-L780) · [Family rank and scale windows](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean#L65-L117).

Suppose a class of steps of relative cardinality $`f`$ has such an orbit with $`O_v/N\to q>0`$, uniformly in that class. The preceding prime-step estimate gives $`Hf/4+o(H)`$ inert log-weight. The factor of two in the actual rational-prime ledger yields normalized recovery $`fq/2+o(1)`$ from this class. Omitted orbits cost at most their omitted retained count in the leading expression since $`O_v\le N_v`$; dropping an entire prime costs at most $`N`$ times its discarded log-weight. Their normalized errors vanish by the served-mass bounds. The two canonical mod-8 class pattern has $`f=1/4,q=1/2`$, giving $`1/16`$ conditionally on an admissible realization. A protected orbit containing one eighth of all retained points in odd positions on one eighth of directions gives $`1/128`$. These are contributions to recovery, not automatically the total across all other steps. [Step equidistribution and discarded-mass accounting](https://github.com/nousentllc/riemann-hypothesis/pull/10) · [Source-based transport to the final ledger](https://github.com/nousentllc/riemann-hypothesis/blob/3dedd2d81a54d046e3c12ef78df9d9fd0c2ad6dc/research/uriel/experiments/actual-gain-study/evidence/transport/TRANSPORT.md).

## Finite tests and kernel scope

In the 32-element controls the fixed numerical-label orders select supports $`\{0,1\}\bmod 8`$ and $`\{4,1\}\bmod 8`$, respectively. Both supports include eight points. At every missing generator exactly four retained positions were odd. Re-evaluating every generator on the same mask at both primes and both lifts gave 64 strict direct winners and 64 strict specialized winners. On every missing shift the normalized recovery $`R/(N_v\lambda)`$ was 0.609359284143 at $`p=1009`$ and 0.609374840224 at $`p=10007`$ (rounded). The eight retained points and fixed $`n=32`$ keep the explicit orbit price visible, so the finite ratio need not be $`1/2`$. The shifted height, fixed price, positive common gain costs and the zero floor were included in the exact comparisons. All 128 evaluations matched the two independent algorithms in the previous study. [Design](DESIGN.md) · [Results](results.json).

Run the CPU tests with the Python standard library. To optionally repeat the cross-study check, set PRIOR_CYCLES to the preceding study's pinned cycles.py and add --previous "$PRIOR_CYCLES".

~~~sh
python3 -B fixed_mask.py --check
~~~

[IncumbentRecovery.lean](IncumbentRecovery.lean) imports the preceding ActualGain supplement. Its kernel endpoints establish the thin cap, upper bound on credit with all first successors missing, lower bound on the unfloored direct gain, lower bound on fallback recovery, and its exact value once the two branch signs are established. The family limits and the passage from a selection rule to a given step profile are separate mathematical arguments. [Kernel receipt](kernel.json).

The portable replay requires the original source export, pinned Mathlib and compiler, the retained-host object inventory and its record, the joint-witness helper directory, and the preceding gain study's local source and receipt. It verifies the imported inventory, replays the four original roots rebuilt outside the common cache, recompiles ActualGain, and checks the new module in a separate checker process. Point the following variables at those checkouts as described in the [prior build guide](https://github.com/nousentllc/riemann-hypothesis/blob/3dedd2d81a54d046e3c12ef78df9d9fd0c2ad6dc/research/uriel/experiments/actual-gain-study/evidence/local/README.md).

~~~sh
python3 -B replay.py --helpers "$JOINT_WITNESS" --original "$RH_ORIGINAL" \
  --mathlib "$MATHLIB_ROOT" --toolchain "$LEAN_ROOT" \
  --retained-library "$RETAINED_LIBRARY" --retained-record "$RETAINED_RECORD" \
  --prior-gain "$PRIOR_GAIN_LOCAL" > /tmp/incumbent-recovery-lean.json
~~~

Optional --staged accepts the four prior rebuilt original objects after matching their hashes against the previous receipt. Neither mode writes into the supplied project or dependency trees.
