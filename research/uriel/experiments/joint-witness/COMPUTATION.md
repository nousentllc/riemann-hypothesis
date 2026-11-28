# An executable prime row and its window controls

We found an explicit instance of the numerical predicate `Rowq`. We carried precisely the same primes and scale into a finite model of the exceptional-set selector and tested the additional hypotheses used by the cohomological proof. The joint attempt fails a known size condition. Its exception sets and their budgets were supplied as fixtures. They have no demonstrated origin in the two-primary or odd-prime representations attached to this prime pair. [Protocol](COMPUTE_PROTOCOL.md) · [Full output, including the prime in decimal](finite_results.json)

## Prime row

With $\varepsilon=1/64$, take the **prime-selection scale** $T=2^{48}$, $n=2^{306}$, $Q_S=4n$, and

$$q=3,\qquad F=2^{1279}-1,\qquad d=6826F+1.$$

The primality certificate for the 1,292-bit $d$ has two steps. Lucas–Lehmer gives residue zero for $F$. With $F\mid d-1$, $F>\sqrt d$, base 2 satisfies $2^{d-1}=1\pmod d$ and $\gcd(2^{(d-1)/F}-1,d)=1$. Consequently for each prime divisor $p$ of $d$, the order of 2 modulo $p$ is divisible by $F$. Then $p\ge F+1>\sqrt d$, which proves primality. The verifier recomputes the Lucas–Lehmer recurrence by folding bits and the two powers by a separate binary exponentiation algorithm. The first qualifying search coefficient was 3,413. [Code](finite_probe.py) · [Independent checks](test_finite_probe.py)

All eleven scalar clauses of $\mathrm{Rowq}(T,\varepsilon,n,q,d)$ passed. In particular $q\equiv3\pmod8$, $d\equiv7\pmod{16}$ and $q\mid d+1$, giving $(-d/q)=1$. The split-prime clause is vacuous because $1.109<T^{\varepsilon/5}<1.110$. The source's `WinPair` divisibility requirements hold as well. The computed enclosures include $1.098<\log q<1.099$, $894<\log d<896$ and $1227<\log X_2(T,\varepsilon)<1229$. The reported upper bound on $\log(4nqd)$ is 1,111. All decisions used rational bounds. For small positive arguments the implementation encloses the series $\log z=2\sum_{j\ge0}t^{2j+1}/(2j+1)$ for $t=(z-1)/(z+1)$, bounding the omitted tail by a geometric series. A separate 90-digit decimal calculation reproduced the comparisons. Replacing $q$ by 11 retained `PrimePair` at conductor one and failed both the upper $q$ box and the pair symbol test. [Scalar Rowq definition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean#L179-L184) · [Exponential boxes and character symbol](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean#L36-L53) · [WinPair](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L27-L39)

The source equivalence uses $n=H.QS/4$ and the very same $H.q,H.d$. Our $Q_S=4n$ is a scalar choice. A typed `PairRow` requires an actual $H:\mathrm{Host}\ R$. A full `PairGood` also requires analytic estimates for induced characters and zero-free boxes. None of these data was supplied by the primality certificate. [Transport into a given host](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean#L167-L173) · [PairGood assumptions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean#L18-L31)

## A common interval, with finite supplied labels

The protocol calls the prime scale $W$. Here $T=X^{1/J}$ denotes that scale and $W$ denotes the selected starting point of the cohomological window, matching their roles in `winPairs`. Put $C_t=401$, $C_K=1$, $R_0=R_3=1$, $\eta=1/128$, $B=C_t/\eta=51328$, $J=16B^2=42{,}153{,}017{,}344$, and $U=\log_2 X=48J$. The preregistered labels $E_A,E_3$ are represented exactly by their exponents

$$\log_2 E_A=405680638918656,\qquad \log_2 E_3=3951845376.$$

The source selector operates on $a=\log_2(E)/C_t$. For $u=\log_2 x$, each label forbids the half-open interval $[a,Ba)$. The algorithm erased both labels in turn and returned $\log_2 W=96$. An independent interval-intersection oracle found no forbidden point in $[96,192]$. Omitting the odd label instead returned a left endpoint of 9,854,976. That point coincides with the omitted label's forbidden left endpoint. Equality matters. The regression suite also compares the selector to this oracle on 390 additional grid cases. [Source recurrence](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean#L6-L45) · [Logarithmic transport](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window.lean#L7-L27)

The registered two-label control supplied one odd component. A separate post-registration computation identifies the actual odd-index set for the primitive conductor-one character as $\{3,7\}$. At that specialization there are three potential contributions, with unknown caps and contents. In addition, $q=3$ fails the later strict comparison $p_1<q$ since $p_1=3$. [Conductor-one computation and source trace](EXCEPTIONS.md)

At $x=2^{144}$, the page exponent can be $e=306$ because $(2+8\varepsilon)\log_2 x=306$. This recovers the same $n=2^e$ used in the row. The cohomological height $t(x)=\lfloor x^{401}\rfloor$ equals $2^{57744}$ and the scale inequality $x^{1/J}\le T\le x$ holds. These are direct computations with the supplied inputs.

The obstruction appears before evaluating any Sha group. The numerical hypothesis of `BShape` asks for $\log(qd)\le X^{\varepsilon/(4J)}=2^{3/16}<2$. Our pair has $\log(qd)>896$. Both later inequalities $q,d>2X^{401}+1$ fail too. The eventual lower threshold $X_0$ is unknown. All three failed inequalities are explicit, independently of that threshold. This example therefore exercises a genuine finite row, examines a conditional selector, and locates a specific point where this finite input leaves the source theorem's domain. [BShape](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L40-L49) · [Where the proof requires these bounds](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean#L70-L96)

## Post-hoc rescaling control

Using the same $T,W,q,d,n$, we tested the source's change of variables $x=kx'$ at a second point. Take $k=2^{1/10}$, $c=k^{2+8\varepsilon}$, $\log_2 x'=2303/16$ and $\log_2 x=11523/80$. Both $k^3$ and $k^{400}$ lie below $T$. The source uses $e(x')$ in the field index. Rounding at $x'$ gives 306, and the scaled inequality $x^{2+8\varepsilon}\le c2^{306}\le2x^{2+8\varepsilon}$ passes. Rounding at $x$ gives 307 and violates the upper bound. $\lfloor x^{400}\rfloor\le\lfloor(x')^{401}\rfloor$ follows by monotonicity on these inputs. These checks compare actual rational exponents and preserve the prime pair throughout. [Source rescaling and field-index application](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean#L52-L81)

At $k=2^{1/2}$ and $x'=W$, cubic window inclusion still holds, but the requested and available heights are the exact integers $2^{38600}$ and $2^{38496}$ respectively. At $k=2^{33}$ the cubic window inclusion itself fails. These counterexamples isolate the two size gates when a finite scale violates the sufficient threshold.

## Reproduce

From this directory with standard-library Python 3.9 or later:

```sh
python3 -B finite_probe.py --out /tmp/joint-finite-results.json
cmp /tmp/joint-finite-results.json finite_results.json
python3 -B -m unittest -v test_finite_probe
```

Python 3.13.2 and 3.9.6 produced byte-identical JSON. Seven tests passed under each interpreter, including the post-hoc rescaling control. The SHA-256 of the published JSON is `30c8f6995f97358c56d688ae1fae359e725aee2a39ef56e099f8eb206807eac5`. These computations use standard integer and rational Python operations. The finite results received no Lean kernel check in this probe.
