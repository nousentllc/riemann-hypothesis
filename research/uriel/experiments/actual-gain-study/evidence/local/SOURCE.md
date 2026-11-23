# The actual branch comparison at one orbit

A served orbit receives the larger of two gains, with zero as a floor. The formalization's local kink estimates one component of a sufficient comparison. The gain definition itself admits a different measurement. It compares positive demand omitted from the baseline and minimum terms on even retained sources against the exact orbit price and any deficit of the baseline. The first odd exponent already gives a rigorous decision interval. Its accuracy depends on the prime and the retained source levels. [Original gain and interaction definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L335-L362)

## Exact identity

Fix an admissible lift \(j\), a prime \(p\), integer level functions \(a,b\) satisfying `InWin`, parameter choice \(P\), and a representative \(t_0\). The first identities also hold at an arbitrary \(t_0\). Let \(T=\mathrm{topsOn}(X,p,t_0)\), and \(E=\{s\in T:\mathrm{IsV}(X,p,s)\}\). On an even central orbit fixed by its base selector, \(E\) consists of the retained even positions in the orbit coordinates. For each retained source \(s\) and odd \(e\), put

\[
 A_s=a_s-2c_G,\quad u_{s,e}=A_s/p^e,\quad
 w_{s,e}=\mathrm{fill}(\mathrm{partner}(s,e))-\kappa_j+c_G,\qquad
 d_{s,e}=(u_{s,e}-w_{s,e})_+,\quad m_{s,e}=\min(u_{s,e},w_{s,e}).
\]

Here \(c_G=4S_c\) and \(\kappa_j=\mathrm{kaJ}(D,j)\). The source hypotheses imply \(A_s,w_{s,e}\ge0\). In particular \(0\le d_{s,e},m_{s,e}\le u_{s,e}\) and \(d_{s,e}+m_{s,e}=u_{s,e}\). Both series are dominated by a geometric series for \(p\ge2\), making the partition legitimate. `Excl` means the first positive visit to a different retained top, at an odd exponent. Repeated visits and returns to the starting top do not meet this predicate. [Cap, distance, baseline and upper branch definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L230-L268) · [Odd-series identity and summability](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/TsumTruncatedShiftLe.lean#L9-L86) · [Level and lift bounds](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L195-L246)

Sum over odd exponents throughout. Write

\[
 B=\sum_{s\in T}\sum_{\neg\mathrm{Excl}}d_{s,e},\qquad
 C=\sum_{s\in T}\sum_{\mathrm{Excl}}d_{s,e}+\sum_{s\in E}\sum_e m_{s,e}.
\]

Then \(g_0=B-dl\) and \(g_U=B+C-dl\). The difference before flooring is \(g_U-\mathrm{Pr}-g_0=C-\mathrm{Pr}\). The common \(dl\) cancels here. In the actual branch choice it returns whenever the baseline is negative. The signed score, the premium above the floored baseline, and the full served gain are respectively

\[
 S=C-\mathrm{Pr}-(dl-B)_+,\qquad M=S_+,\qquad
 G=\max(g_U-\mathrm{Pr},g_0,0)=(B-dl+(C-\mathrm{Pr})_+)_+.
\]

Exactly \(G=(g_0)_++M\). On the nonzero branch of `gainP`, every representative contributes \((g_0)_+\), and only served representatives add \(M\). For a single orbit, the source's \(S_v\) is exactly the ceiling of the sum of those premiums over lifts, cast from the integers back to the reals. The separate stop guard sets the entire `gainP` to zero when the central step vanishes or the prime exceeds \(X''\). These identities require neither a large-prime cutoff nor box upper bounds. [Source baseline and upper branch](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L241-L268) · [Source `Sv`, `ioP`, `gainP`](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L335-L361)

At \(p\ge p_0\), with \(o_s=X.\mathrm{off}(j,(\mathrm{false},s))\), the price and common deduction are exactly

\[
 \mathrm{Pr}=\sum_{s\in T\setminus E}(o_s-\kappa_j)+K.\mathrm{Pr1}\,n_P(w''+\eta+c_G+N_m),\quad
 dl=K.\mathrm{dl1}\,n_P N_m^2\log_p(2a_*)+K.\mathrm{dl2}\,|T|\log_p^2(2a_*).
\]

The symbol \(a_*\) denotes the scale `L.sc.a`, distinguished from individual integer levels \(a_s\). At a central prime \(n_P\) equals the orbit step's additive order. The price keeps the signed lift contribution. A gain estimate cannot discard the fixed price or \(dl\) solely from the definitions. [High-price branch](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L241-L269)

## A finite decision interval

On a central nonzero step, exponent one is excluded precisely when the successor \(s+h_P\) is retained. There is no earlier positive visit to check at that exponent. Let \(u=u_{s,1}\), \(w=w_{s,1}\), and sum the following two columns to obtain \(C_1,B_1\).

| Source and successor | First credit \(C_1\) | First baseline demand \(B_1\) |
|---|---:|---:|
| Even source, retained successor | \(u\) | \(0\) |
| Even source, absent successor | \(\min(u,w)\) | \((u-w)_+\) |
| Odd source, retained successor | \((u-w)_+\) | \(0\) |
| Odd source, absent successor | \(0\) | \((u-w)_+\) |

The entire first column of an even-to-retained edge becomes credit, independently of the target fill. An odd-to-retained edge contributes only demand over the cap. Both kinds of retained-to-hole edge can sustain the baseline. The retained positions' parity is determined by the source base selector, and the cap includes \(-\kappa_j+c_G\). Merely knowing the number of occupied positions does not determine either column. [Central partner and position transport](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L345-L366)

Beyond exponent one, the total supply of a row is \(A_s/[p(p^2-1)]\). At an even source, the remaining baseline and credit terms together spend this geometric tail exactly. At an odd source their sum is the remaining positive demand, bounded by the same tail. Consequently the joint estimate is

\[
 B\ge B_1,\quad C\ge C_1,\qquad (B-B_1)+(C-C_1)\le R,\qquad R=\sum_{s\in T}\frac{A_s}{p(p^2-1)}.
\]

Define \(S_1,M_1,G_1\) by replacing \((B,C)\) with \((B_1,C_1)\) in the exact formulas. The supplement establishes the three intervals \(S_1\le S\le S_1+R\), \(M_1\le M\le M_1+R\), \(G_1\le G\le G_1+R\). In particular \(S_1>0\) certifies a strict upper-branch improvement, while \(S_1+R\le0\) certifies zero improvement. For an overlap with zero, the first-exponent interval by itself does not classify the branch. No sign on the actual gap is assumed.

There is a sharper credit-only bound when \(p^3\ge2H\) and \(H=X'\). All excluded terms with \(e\ge3\) see retained cells with cap at least \(b'\), whereas \(A_s/p^e\le 2a_*/p^3\le b'\). Their positive parts vanish exactly. Only even sources then contribute to \(C-C_1\), with error at most \(\sum_{s\in E} A_s/[p(p^2-1)]\). `InWin` suffices because the proof needs a lower bound on the target level. Neither this saving nor the exact even-to-retained cancellation needs the upper `winB` endpoint from the prior kink calculation.

For \(N=|T|>0\), \(\lambda=b'/x\), and \(p\ge\sqrt{H}\), the elementary normalization gives \(R/(N\lambda)\le 2x/[\sqrt{H}(1-p^{-2})]\). This vanishes along the specified scale at fixed positive \(\epsilon\). It controls the error of the first-exponent *formula*, including its dependence on the actual levels, directed adjacency, price and deduction. The estimate supplies no sampled arithmetic orbit, prime average, or family-wide sign of the score. [Scale definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataParams₂.lean#L27-L39)

## Exact evaluation with a given witness

The one-exponent interval is useful when only a few inputs are available. With the complete witness data the infinite series can also be eliminated exactly. The original bounds give \(w_{s,e}\ge1\) for every partner, since its fill is at least one and \(c_G\ge\kappa_j\). Take any natural \(N\) with \(p^N\ge2a_*\); existence follows from \(p\ge2\). For \(e\ge N\), all retained sources satisfy \(A_s/p^e\le1\), and hence all positive demands vanish. Compute the kept and excluded positive demands over \(e=0,\ldots,N-1\). Their complementary minimum series then equals

\[
 \frac{p}{p^2-1}A_s-\sum_{e<N,\ e\ \mathrm{odd}}d_{s,e}.
\]

The same cutoff works for every retained source and admissible lift at that prime and scale. `cutoff_exists`, `demand_zero_after`, and `finite_column` formalize the cutoff and all three equalities. This is finite dependence on supplied levels, offsets and classifications. A real-valued offset given only by bounds still cannot generally be evaluated, and a witness chosen by existence is not recovered by the identity. Certified intervals can nonetheless settle a strict sign when the resulting enclosure stays on one side of the switch. [Original lower bound on all fills](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L203-L225)
