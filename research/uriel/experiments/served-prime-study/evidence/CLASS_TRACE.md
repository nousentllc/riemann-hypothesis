# The prime class of a moving host

A prime counted by the high-prime allowance must pass two different quadratic sign tests. The same family retains enough analytic information to evaluate their joint prime log-weight uniformly at the moving cutoff. Put \(Z=X'=\exp(x^{\varepsilon/3})\) and fix \(0<\varepsilon<1/52\). The conclusions here refer to every index permitted beyond the family thresholds for the row and the zero-free boxes.

## What the prime class means

For prime \(p\) and actual host conductor \(M=Q_S qd\), the source proves
\[
 H.\mathrm{cls}(p)=\mathrm{inertClass}
 \quad\Longleftrightarrow\quad
 p\nmid M,\quad \left(\frac{-d}{p}\right)=-1,\quad
 \left(\frac{-q}{p}\right)=-1.
\]
It identifies the Artin sign \(\mathrm{psAt}(p)\) with the second Jacobi symbol by the host's sign-character property and quadratic reciprocity. A prime with signs \((-1,+1)\) instead belongs to the signal class. The exception \(p=2\) is ramified. The source's \(Q_S\) can include extra factors, so removing only \(q,d\) from a general prime list would use a larger set. [Prime classification and conductor exclusion][class] · [Artin sign equals the quadratic symbol][psat]

The auxiliary row chooses distinct odd primes \(q\equiv3\bmod8\) and \(d\equiv7\bmod16\). Define \(\chi_d,\chi_q\) by the primitive quadratic characters for \(-d,-q\). Away from \(M\) their values at primes equal the Jacobi symbols above. Then the indicator for inertClass equals
\[
 \tfrac14(1-\chi_d(p))(1-\chi_q(p)).
\]
The three nonprincipal functions in the expansion have primitive conductors \(d,q,dq\). For a prime \(r\equiv3\bmod4\), reciprocity identifies \((-r/a)\) with the quadratic character \(a\mapsto(a/r)\) on odd units. The nontrivial Legendre character has conductor \(r\). For the product, a residue that is a nonresidue at one factor and 1 at the other exists by CRT. This rules out factoring the product through either proper prime factor, and both components take values in \(\{\pm1\}\) on units. The construction in the original code twists a primitive character by each new coprime odd prime and checks the agreement of its primitive representative on units. This applies also on powers of primes outside \(M\), by multiplicativity. [Primitive twists used in the construction][primitive] · [Identification of the two coordinates][coordinates] · [All three induced functions][three]

## Which scale belongs to which witness?

The host theorem fixes positive constants before quantifying the scale, ranks and the prime pair. Its explicit construction uses the row at \(Y=x\), retains \(q,d\) when it replaces the top set \(TT\), and returns both the thin-character bound and the row/box information. The more abstract family statements permit a witness \(x^{1/J}\le Y\le x\) for each family index. The \(Y\) offered for the boxes need not be identified with the one offered for the row. Both apply to the very same \(D=\mathrm{Fm.D}(x,i)\). Its three characters therefore retain both their zero-free information and an upper bound on conductor size. [Host statement with quantifier order][host1] · [Same prime pair after updating the retained set][host2] · [Exact family contracts][boxes] · [Original proof takes separate row and box witnesses for the same index][same]

In detail, the row guarantees splitting of \(-d\) for primes up to \(Y^{\varepsilon/5}\), and also at \(q\). At \(Y=x\) this forced splitting ends at \(x^{\varepsilon/5}\), which is much smaller than \(p_0=k^2 x^{26}\). Even that stronger row does not decree that every prime below \(Z\) splits. The ranks place \(k\le2x^{9/2+10\varepsilon}\), hence \(p_0\le4x^{35+20\varepsilon}\). Its prime log-weight divided by \(Z\) tends to zero, because \(\sum_{p\le p_0}\log p\le p_0\log p_0\). The row also gives
\[
 \log M\le 2Y^{\varepsilon/5}(\log Y)^2
          \le 2x^{\varepsilon/5}(\log x)^2
\]
once \(1\le Y\le x\). This is uniform in the family index. [Rank ranges, row and split-prime constraint][row] · [Cutoff and lower threshold][scale]

## An unsmoothed estimate already available upstream

Each of the three nontrivial functions has its own zero-free box in \(\mathrm{Boxes\_at}\). In Lean the box quantifies over primitive representatives agreeing with the indicated function on integers coprime to \(8qd\). Restrict its complex rectangle to the real axis. For every such representative there are no zeros at real \(\beta\) with \(1-1/400<\beta<1\). The primitive principal character of conductor one satisfies the exceptional-zero implication vacuously. The heights are positive products of exponentials. [Functions included in the boxes][boxes] · [Region and induction definition][defs] · [Exceptional-real-zero predicate][noexc]

The original theorem \(\mathrm{QH.psi\_thin}\) gives constants \(A,c>0\) depending on that fixed exceptional-zero width. For every primitive character meeting its premises, every \(\lambda\ge\max(1,\log N)\), and \(u\ge e\),
\[
 |\psi_0(\chi,u)|/u
 \le A(\log u+\lambda)^2
     \exp\!\left[-\frac{c\log u}{\lambda+\sqrt{\log u}}\right].
\]
Here \(\psi_0(\chi,u)=\sum_{n\le u}\Lambda(n)\chi(n)-{\bf1}_{\chi=1}u\). This is an unsmoothed estimate. A separate original theorem integrates it to bound a weighted sum involving the logarithmic derivative. That integration is unnecessary for the present use. The premises are sufficient before the RH conclusion; the derivation does not apply GRH to the moving characters. [Unsmoothed estimate and proof inputs][psi] · [Definition of the centered sum][psidef] · [Its use upstream of the integrated bound][integration]

Take \(t=\log Z=x^{\varepsilon/3}\). Since \(\log M=O_\varepsilon(t^{3/5}(\log t)^2)\), for large enough \(x\) we may take \(\lambda=t^{2/3}\) simultaneously for these four characters. The normalized error in each of the four sums is at most
\[
 E(t)=4A t^2\exp[-(c/2)t^{1/3}]\longrightarrow0 .
\]
The constants for the unsmoothed theorem precede the choice of the family, and the threshold in this last comparison may depend on \(\varepsilon\). This quantitative separation is what allows the field and conductor to vary.

## From von Mangoldt weights to prime log-weight

Replacing each of the four von Mangoldt sums by a prime log-sum costs at most \(\sqrt Z\log Z\). For each prime \(p\le\sqrt Z\) its powers \(p^j\le Z\) with \(j\ge2\) contribute in absolute value at most \(\log Z\) in total. Outside the conductor the quadratic projector is exact; the extra primes dividing \(M\) cost at most \(\sum_{p\mid M}\log p\le\log M\) because each unrestricted projector has magnitude at most one. Using \(p<Z\) instead of \(p\le Z\) costs at most \(\log Z\). Thus for the unserved-or-served union \(\mathcal I=\{p\text{ prime}:p_0\le p<Z,\ H.\mathrm{cls}(p)=\mathrm{inertClass}\}\),
\[
 \left|\frac1Z\sum_{p\in\mathcal I}\log p-\frac14\right|
 \ \le\ E(t)+\frac{\log Z}{\sqrt Z}
       +\frac{\log M+\log Z+p_0\log p_0}{Z}
 \ \longrightarrow0 .
\]
The \(1/4\) is a moving-scale weighted limit. It is independent of any finite-host observed frequency. A further comparison with the chosen drop set is necessary to conclude a limit for the served subset. The separate drop trace supplies the relevant constraints.

The [separate representation replay](class_lean/representatives_verification.json) kernel-checked the three exact conductors, the induction agreements and the evaluations at every natural number. The [analytic replay](class_lean/verification.json) checked the box-to-unsmoothed-estimate implication, its envelope and the decay of that envelope. The final passage from the four estimates to the moving prime limit is a mathematical deduction here. An individual quadruple of concrete primitive character values is computable once \(q,d,p\) are supplied. The positive constants, family thresholds and selected rows in this argument are existential.

[class]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/HostCls.lean#L111-L145
[psat]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/HostCls.lean#L178-L207
[primitive]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/PairRows.lean#L7-L65
[coordinates]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/Joints.lean#L947-L974
[three]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/Joints.lean#L982-L1021
[host1]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HostExistenceOfChoices.lean#L179-L197
[host2]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HostExistenceOfChoices.lean#L246-L285
[boxes]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/MainIn.lean#L12-L38
[same]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/MainSup.lean#L48-L63
[row]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean#L28-L84
[scale]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/DataParams₂.lean#L29-L45
[defs]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean#L36-L58
[noexc]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean#L65-L72
[psi]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean#L385-L399
[psidef]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/PeriodIntegrals/ExplicitFormula.lean#L5-L11
[integration]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/MeanSquareBounds/Thin.lean#L10-L18
