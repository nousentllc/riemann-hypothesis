# One target, two winning branches

On the same oriented orbit, at the same prime and lift, the odd top at 3 pays its full pointwise charge in each of two experiments. Moving the single even top from 0 to 4 switches the winning gain formula. Including the nearest-even component of the prime tax preserves the ordering of the final gaps throughout the primary experiment, even when its remaining costs have arbitrary common fractional parts. These are exact finite evaluations of the local formulas conditional on service.

## Experimental unit and measurement

Every orbit has a chosen base of zero, step +1, and even order n. Position s is even or odd relative to that base. We hold p, the lift j, the top heights A and B, the offsets, and all coefficients fixed when comparing masks. On a top the unshifted fill F is B+λ. Elsewhere it is λ/n. The scale height is a distinct number, denoted a. We choose A=ceil(a) and specify integer B. In the actual numerical datum the integer inputs are floors of top values and the offset is derived from the original weight minus that integer. Our A, B and offsets can be used as exact integer inputs to the local formulas. The experiment does not extract these integers from the source's existential global datum. [Integer levels and offset][int] · [Orbit, fill and position][loc]

Write κ for the lift shift, c for cG, H=A−2c and C=F−κ+c. An odd exponent e takes s to s+e modulo n. The direct gain G subtracts the common loss dl from the sum of (H/p^e−C)_+ over all tops and all odd e, skipping the first arrival at a different top. The other branch U is gU−Pr. Here gU sums the geometric weights H/p^e at every top, subtracts the minima min(H/p^e,C) at odd starting tops, then subtracts dl. The high-regime Pr has a variable cost (#odd)(λ−κ) and a fixed cost Pr1·n·(λ/n+η+c+Nm). The gross odd geometric sum per top is H·p/(p²−1). Q sums (A/p^e−F)_+ over all tops and odd e. The comparison for a served orbit is max(G,U,0), with the maximum taken after the sum over tops. The terminal demand is Q, while the intermediate shifted demand replaces F by F−κ. [Gain formulas][branch] · [Service and selection][served] · [Terminal demand][terminal] · [Shifted and unshifted bounds][demands]

The pointwise kink term at an odd y is λ−κ−clip. If d is its closest preceding even top distance, clip=min(λ,(A/p^d−B)_+). With no even predecessor the source's dMinus=0 sentinel gives clip=0. The signed orbit charge also subtracts the unused even minimum, the entire sum of unshifted minima over even starts less the selected min(B+λ,A/p^d) edge for each matched odd end. Equivalently, the signed orbit charge is (#odd)(λ−κ) + M − the sum of all even minima, where M sums the selected min(B,A/p^d) edges. The number M also enters the prime tax. The program computes both the charge before taking its positive part and its positive part. [Nearest preceding even top][nearest] · [Injection underlying the inequality][kink] · [Orbit version and fills][kinkhh]

## Registered primary results

There are 255 nonempty masks on the order-eight cycle. With p=5, j=1, κ=6, A=1563, B=150, λ=64 and the positive coefficients in DESIGN.md, 212 favor U strictly and 43 favor G strictly. The unshifted pre-tax gap Q−max(G,U,0) is positive in 34 cases and negative in 221. These are unweighted counts over *all* subsets. The proof chooses a thin top set subject to simultaneous tests, so this enumeration gives no frequency in the actual family. The small primary constants also violate the actual bounds κ≤Nm and κ≤Sc. Every table entry below is rounded only for display. Exact fractions are in results.json.

| Tops | Closest predecessor of odd top | Odd row | Signed orbit charge | G | U | Q | Pre-tax gap |
|---|---:|---:|---:|---:|---:|---:|---:|
| {0} | — | — | −16.521 | 315.256375 | 317.776042 | 309.104 | −8.672042 |
| {3} | absent | 58 | 58 | 315.256375 | 251.256375 | 309.104 | −6.152375 |
| {0,3} | 3 | 58 | 49.479 | 622.665750 | 575.657417 | 613.704 | −8.961750 |
| {3,4} | 7 | 58 | 41.499006 | 323.337750 | 369.657417 | 412.208 | 42.550583 |
| {0,1} | 1 | −6 | −14.521 | 323.337750 | 575.657417 | 412.208 | −163.449417 |

Both headline masks have clip=0 at the same target, y=3. In {0,3}, the rays joining the two tops first do so at distances 3 and 5. Neither exceeds the direct cutoff there. G recovers 5641/120 over U. In {3,4}, the odd top reaches a different top one step later. Its first-hit excess of 509/5 is excluded from G. U wins by 138959/3000. Reversing the adjacent arrangement to {0,1} retains the values of G and Q but changes which start is even and raises U by 206. The full pointwise charge fails as a branch classifier.

## Paying the tax once

In the high-prime formula tIf=M+C, where C includes two threshold terms and 2nc. The threshold terms depend on the orbit length, prime, constants and number of tops. For these two masks they coincide. When there is one served orbit, the prime tax is ep + m(ceil(M+C)+Dp+1) for nonnegative M+C. For the one-lift primary ablation take ep=0, both threshold coefficients zero and DI=0. This gives C=32, Dp=0. It makes the tax calculation reproducible while keeping the contributions of the first-hit and nearest-even mechanisms visible. An actual Ranks instance requires m even and at least two. A separate two-lift experiment follows below. [High-regime Dp][degree] · [High-regime tIf][taxlocal] · [Prime-level rounding and service][served] · [Lift count][ranks]

| Tops | M | ceil(M+32) | Prime tax | Q+tax−selected gain |
|---|---:|---:|---:|---:|
| {0,3} | 1563/125 | 45 | 46 | 148153/4000 = 37.03825 |
| {3,4} | 1563/78125 | 33 | 34 | 918607/12000 ≈ 76.550583 |

There is also an exact robustness calculation. The difference between the two values of M is 975312/78125, strictly between 12 and 13. For any common C≥32 the difference of their ceilings lies in {12,13}. Equal ep and Dp cancel when we compare the two masks. The pre-tax gap of {3,4} exceeds that of {0,3} by 154537/3000. The corresponding **taxed** gap exceeds it by either 115537/3000 or 118537/3000. This conclusion is conditional on a shared prime tax profile and on the primary scalar gain inputs.

## Can the full row correction disappear from the net gain?

The registered zero-loss, zero-shift scaling panel isolates a precise mechanism. Let E sum the first-hit positive excess omitted by G, and let V be the unshifted even-start minimum sum. Exact cancellation in the definitions gives G=Q−E≥0 and Q−U=(#odd)λ−V. Thus the pre-tax gap is min(E,(#odd)λ−V). This identity applies to this ablation. It does not absorb taxes, fixed costs or shifts into E.

Take a=p³/2, B=floor(a/(2p)), λ=B/4, n≥8 even, and exactly the two displayed tops. In either configuration the first successor of the even top is empty, so V≤λ/n + A/[p(p²−1)] by bounding the odd tail from exponent three. In {0,3} both first arrivals at a different top have distance at least three, giving E=0. The registered range has λ>V, hence the selected gain equals Q. In {3,4} the odd-to-even first hit has excess A/p−(B+λ)≥3λ. The U branch therefore determines the pre-tax gap λ−V. In both configurations the individual odd row is exactly λ. The signed orbit charge is λ+M−V, and M≤A/p³, so its ratio to λ tends to one as both p and n grow. The pre-tax gaps divided by λ approach zero and one respectively. Omitting later laps or keeping the per-top charge alone would fail to distinguish these regimes.

At p=1009 and n=32 the signed orbit charges divided by λ are 0.968750 and 0.968742. The corresponding pre-tax gaps divided by λ are 0 and 0.968742, respectively. Exact expressions differ before rounding because the latter cycle's matched edge contributes a small M. All 18 registered (n,p,mask) cases passed the exact identity.

## Positive costs, rank relations and final two-lift ledger

The first follow-up uses strictly positive dl1, dl2 and Pr1, sets Nm=44 and κ=15≤Sc=32, and requires Nm+1≤thin. Both winners persist at p=101 and 1009. The resulting Q−gain divided by λ is 0.190684 and 2.159623 for the two masks at 101, and 0.00001914 and 1.968738 at 1009. The overshoot above one for the U winner includes the fixed cost on the whole orbit. This follow-up still fails Nm≤Sc, 100≤Sc and the rank lower bound on t. Retaining it makes those omissions auditable. [Rank structure][ranks] · [Nm and Sc bounds][scale]

The second follow-up enforces every inequality in the displayed Ranks structure for a cyclic frame of order 32. Its scalar choices are k=64, m=2, t=71, Nm=208 and κ₁=68, κ₂=140. It sets Δ=Nm·m^10=212992, Sc=4kΔ=54525952 and c=4Sc. Both lifts use unit gain coefficients. At each p, a=p⁹/2, B=floor(a/(2p)) and λ=B/16. The one-orbit service condition and the high-prime branch are assumptions. The remaining discriminant conditions, simultaneous scale identities, windows, host field and arithmetic class are unverified. [Rank structure][ranks] · [Discriminant conditions][delta] · [Scale-curvature identity][sceq]

For this two-lift panel, the prime-level gap adds both unshifted demands, subtracts both selected gains, then adds exactly one tax ep+m(ceil(M+2nc)+1). The tax thresholds, DI and ep are ablated as above. The normalization 2λ counts the odd top once at each of the two lifts.

| p | Winner at both lifts on {0,3} | Taxed gap/(2λ) | Winner at both lifts on {3,4} | Taxed gap/(2λ) |
|---:|---|---:|---|---:|
| 1009 | G | 0.000031431685 | U | 1.968718568287 |
| 10007 | G | 0.000000319552 | U | 1.968749680448 |

At p=1009, the exact taxes are 1055229706687112868 and 27917287428. A long preceding edge makes the tax small relative to λ even when its absolute value is large. An adjacent edge in the opposite direction can still make the direct gain uncompetitive. This is a separation visible inside explicit finite ledgers, including positive gain costs and the prime-level ceiling. The examples do not imply that a witness of the original construction realizes either mask.

## Other controls and residual uncertainty

* Raising the shared loss subtracts equally from G and U. With dl1=1000 the zero branch strictly wins on both singleton controls. On {3,4}, the solved coefficient Pr1=156959/288000 yields an exact positive tie at 1293351/4000. Adding one to this coefficient makes G the unique winner.
* Repeated arrivals may contribute. At n=8, p=5, a=p¹⁵/2, B=0, λ=1 and c=κ=0, the later positive arrivals at a distinct top on {0,1} sum to 15256835938/1953125. Deleting all such arrivals would understate G. In a separate zero-cap control, summing the infinite geometric rays gives Q=2605/4 exactly.
* Two served orbits with the primary local masks give an independently selected sum exceeding the maximum taken after summation by 138959/3000. The lift radius Sv also has its own ceiling. With n=32, p=101 and {3,4} in the first follow-up, rounding the sum of the two raw service increments gives 42375329. Rounding each before adding gives 42375330. The source uses the former. [Gain and radius][served]
* All code uses integers and fractions. One evaluation groups odd exponents by residue modulo n. A positive-cap ray has finitely many positive excesses, and a zero-cap ray is geometric. A separate evaluator scans odd exponents in order, includes the complete first lap, then sums geometric tails once every remaining positive cap dominates the largest outstanding height. The calculations compare every aggregate between the two evaluators on every mask. The orientation, prime, service flag and chosen parameter specialization are shared inputs, so agreement does not verify those modeling decisions.
* The next decisive arithmetic datum would match one actual selected prime, canonical representative, top pattern, lift values, floors and served decision at the same global input. If that becomes available, additional weight on the final discrepancy requires the frequency and aggregate contribution of such patterns. This program evaluates the supplied local data and does not extract the global input or select the host. No Lean proof was built by this Python experiment.

Run `python3 cycles.py` from this directory and compare its stdout to results.json. Supply `--all-masks PATH` for the complete 255-mask table. DESIGN.md precedes the primary run, FOLLOWUP.md registers the first strengthening, and RANK_FOLLOWUP.md registers the second. The ceilings, zero-cap test and tax-residual comparison are validation controls documented after the primary result.

[loc]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L62-L104
[branch]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L142-L178
[served]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L189-L228
[int]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L311-L316
[terminal]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L333-L354
[demands]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L99-L131
[nearest]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L207-L225
[kink]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L136-L169
[kinkhh]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean#L369-L437
[taxlocal]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L129-L137
[degree]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean#L106-L113
[ranks]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/Params.lean#L6-L36
[scale]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L52-L79
[delta]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataParams.lean#L193-L202
[sceq]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataParams₂.lean#L144-L148
