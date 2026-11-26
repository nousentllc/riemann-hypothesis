# Where the two Riemann-hypothesis source editions meet

**Research note · 25 November 2026.** This comparison fixes the original edition at `40e56bab026552e089d7afcfeff08d2defb9c005`, the readable edition at `e063a923620ee7787b4a1270421478645bf66bdb`, and the Nous ramified square-dilate release at standalone revision `d9b1a208b1d0b65b1cf9be8be42d8f3909d5aff5`. The two editions give different organizations of the argument. A claim about one pin needs its own justification at the other. The source links below identify the files used in the comparison.

## I. What is actually shared by the two prime sums?

Write $G_1$ for the old centered conductor-one ramp (`Deduction.G`), $G_χ$ for `Deduction.Gchi`, and $R_{d,q}$ for the readable edition's `New.primeRemainder d q`. For an odd prime $d$, take $χ_d$ to be the quadratic twist of the level-one character in the readable edition. The precise comparison at modulus one is

$$
R_{d,1}(y)=\frac{G_1(y)-\Re G_{χ_d}(y)}{y},\qquad y>0 .
$$

This includes the centering constant. A common smoothing shape alone would only identify the finite prime sum. The level-one remainder occurs explicitly at the auxiliary scale $x_1$ in the readable edition's arithmetic estimate, making this identity relevant even though the main modulus of its eventual bound must be divisible by 18,480. [Older character and family definitions](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean) · [New remainder and level-one constant](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/Zeros/PrimeError.lean#L140-L163) · [Auxiliary scale in the arithmetic bound](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/OneSidedBound.lean#L29-L67)

### Derivation and its checks

1. At positive $y$ and integer $n≥1$, $(y/n-1)_+/y=(1/n-1/y)_+$. Thus the difference of the old two raw ramps divided by $y$ has coefficient $\Lambda(n)(1-χ_d(n))$. The apparent extra term $n=0$ in the old range vanishes. The weight at a power of $d$ occurs once because the character there is zero.
2. Dividing the old principal ramp by $y$ contributes $-\log y+1+γ$ to its centering. Subtracting the old nonprincipal ramp contributes $-\Re (L'/L)(1,χ_d)$. Upstream's `re_logDerivMean_one_eq_add_re_logDeriv` gives $\Re G_{d,1}^{\mathrm{mean}}(1)=-1-γ+\Re(E'_{χ_d}/E_{χ_d})(1)$. The twist is nonprincipal for odd $d$, so its entire function $E_{χ_d}$ is its Dirichlet $L$-function. Since the new definition *subtracts* the mean, both constants and signs agree. [Twist identity and nonprincipality](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/Analytic/EntireLFunction.lean#L42-L66)
3. The accompanying Lean file uses the old definitions for the normalized, centered signed contrast. Identification with the literal upstream declaration uses the named new-edition lemmas above. These are distinct verification steps. The comparison does not link the two editions in one Lean environment.

**A hand check.** With $d=7,q=1,y=4$, the uncentered contrast is $\log(3)/6$. The character is $+1$ at 2 and $-1$ at 3. The term at the endpoint 4 has zero kernel. At $y=8$ the coefficient of $\log(7)$ is $1/7-1/8=1/56$. The executable control treats each $\log(p)$ as a formal symbol with rational coefficients. Across seven cases at levels 1 and 4, the explicit residue filter agrees coefficient by coefficient with the signed character ramps. Changing the twist subtraction to addition fails all seven. These checks concern finite sums. They neither evaluate $L'/L$ numerically nor test an asymptotic assertion. [Exact controls](finite_controls.py)

### What extends to general modulus

Here is the written dictionary for $q≥1$, $d$ an odd prime coprime to $q$. For any character $ψ$, put $e_ψ=1$ if it is principal and zero otherwise. Write $E_ψ$ for its upstream entire normalization, and define

$$
H_ψ(y)=\sum_{1≤n≤y}\Lambda(n)\Re ψ(n)(1/n-1/y)
-e_ψ\log y+\Re(E'_ψ/E_ψ)(1)+e_ψ .
$$

Then the definitions and character orthogonality give the exact expression

$$
R_{d,q}(y)=\frac1{\varphi(q)}
\sum_{ψ\bmod q}\bigl(H_ψ(y)-H_{ψχ_d}(y)\bigr).
$$

To check the finite terms, average $ψ(n)$ over the full group. The average is one in the identity residue class and zero elsewhere, including nonunits for $q>1$. The twisted average contributes the same indicator times $χ_d(n)$. For the constants, exactly one untwisted character is principal and every twist in this formula is nonprincipal. Thus the sum gives $-\log(y)/\varphi(q)-\Re G^{\mathrm{mean}}_{d,q}(1)$, including the unit constant divided by $\varphi(q)$. For a principal character at level $q>1$, the logarithmic derivative of the regularized imprimitive $L$-function retains the Euler factors at primes dividing $q$. Substituting the conductor-one zeta constant in that term would change the formula. The all-modulus expression is a written deduction here. The finite tests at levels 1 and 4 cover only the raw sums. [Definitions of the mean and remainder](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/Zeros/PrimeError.lean#L43-L68)

### Why a dictionary of observables does not transfer the window theorem

| | Original localized criterion | Readable remainder criterion |
|---|---|---|
| Input | A fixed finite character family with *strictly positive* weights. A principal member must have level one. | An average of untwisted terms **minus** their quadratic twists. Its raw arithmetic coefficients $1-χ_d(n)$ are nonnegative. These are two different senses of positivity. |
| Where the bound must hold | For every starting threshold there is a later $Y$ such that the upper bound holds throughout $[Y,Y^{1+δ}]$, with $0<θ<1, δ>0$. | For every prime $d$ in the admissible class there is a coefficient $A$ and an eventual bound for **every** sufficiently large real argument. The threshold can depend on $d$. |
| Exponent on the raw scale | $C y^θ$ for the old family. | $A y^{β-1}$ for the normalized remainder, or $A y^β$ after multiplying by $y>0$. |
| What protects the pole argument | The old criterion applies to its admissible family; its window hypothesis controls the positive part of that same observable. | The transform counts untwisted zero orders minus twisted zero orders. Given a putative zero $ρ$, the criterion chooses a twist with no zeros in the required bounded-height region. There the subtraction cannot cancel the candidate zero. |

Thus an eventual upper bound restricts to every sufficiently late window **of its own observable**. Conversely, cofinal good windows can leave arbitrarily late gaps. Even on a common window, two upper bounds on individual summands do not upper-bound their difference without lower control on the subtracted one. The twist selection is doing mathematical work that rescaling the exponent cannot supply. [Original localized criterion](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean) · [Current criterion and choice of twist](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/Zeros/Criterion.lean#L37-L76)

### Where the displayed coefficient comes from

For $18{,}480\mid q_0$, prime $d\equiv q_0/2-1\pmod{q_0}$ and $ε>0$, the source starts with an eventual integer bound having coefficient $C=64\varphi(q_0)+3$ and exponent $t=-1/2+6δ$. For all sufficiently large integers $x$ the proof obtains auxiliary data adapted to **that** $x$, including bounds at a later $x_1$. At $y≥2$, replacing $y$ by its floor costs at most $26/y$, and $\lfloor y\rfloor^t≤2y^t$ for $-1≤t≤0$. The real-variable coefficient is therefore $2C+26=128\varphi(q_0)+32$. Choosing $6δ≤ε$ gives the stated exponent. At $q_0=18{,}480$ this coefficient is $491{,}552$; the theorem does not output a first valid $y$. The upgrade from selected windows to an eventual statement in this comparison is a change in the arithmetic argument and the observable. Keeping the coefficient explicit explains neither upgrade on its own. [Auxiliary data and integer estimate](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/OneSidedBound.lean#L69-L153) · [Passage to real scales](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/New/Reduction/OneSidedBound.lean#L196-L231)

## II. Can the current density bounds reproduce the ramified example?

Fix the base completion $K=\mathbb Q_2(\sqrt2)$, coefficient order $O=\mathbb Z_2[\sqrt2]$, and the released basis $(1,i)$ of the Gaussian quadratic algebra, with $i^2=-1$ and Gaussian conjugation fixing $K$. Our coordinate lattice uses $a+bi$ with $a,b\in O$ in each of three Hermitian coordinates. Denote this coordinate order by $B=O[i]$. The paper's target $4$ has original regular fiber mass $257/128$ for normalized base Haar measure. A direct application of the readable semilocal bound would require identifying its integral vectors with this same lattice and its mass with this same numerical normalization. [Released endpoint](../ramified-square-dilates/dilates/DilateEndpoint.lean) · [Gaussian basis and Gram matrix](../ramified-square-dilates/bridge/RamGlobal.lean) · [Identification of the literal lattice](../ramified-square-dilates/dilates/DilateTransport.lean)

| Required item | Comparison for this example |
|---|---|
| Ambient trace-one element in `Place` | $1/2$ has Gaussian trace one in the field algebra. This settles one algebraic field at the ambient level. |
| Integral trace-one element in `IntegralPlace` | **Obstructed for $B$.** Every $a+bi$ has Gaussian trace $2a$. Reducing the first dyadic coefficient of $2a=1$ modulo 2 gives $0=1$. The accompanying Lean lemma uses `QuadraticAlgebra RamField.O $-1$ 0` itself. |
| Integral skew unit and inverse | $i$ is skew, and $i^{-1}=-i$ also belongs to $B$. This algebraic requirement presents no such obstruction. |
| Haar and Fourier normalization | The old `IsStdV` gives the base valuation ring volume one; the old source and target measures are built from specified coordinates. The readable structure also prescribes the skew-target Haar measure, a measure-preserving split, self-duality for an additive character, modulus/index agreement, and a Fourier kernel bound of one. No identification of these data has been proved here. |
| Rank and ideal-zeta estimate | There are three Hermitian inputs and six base coordinates. The upstream semilocal lattice bound requires $2μ+1≤3$, hence $μ≤1$, plus $\zeta_R(μ)≤2$ and a character trivial on traces. The standard-form kernel theorem uses $2μ+2≤3$, hence $μ=0$ if invoked at this rank. Passing the rank inequality alone does not prove the zeta hypothesis. |
| Continuity and uniqueness | The released `IsGramFib` is expressed through the regular locus and compactly supported tests supported there. The readable `Place.IsDisintegration` requires continuity and finiteness for every compactly supported continuous nonnegative test over the full skew target, plus a joint integral identity. Pointwise uniqueness applies once two families satisfy that *same* disintegration. A regular nonzero target comparison may be narrower and still worthwhile. |

[Upstream ambient place and trace element](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/General/Measure/QuadricDisintegration.lean#L31-L93) · [Finite-place normalization](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean#L59-L85) · [Continuity and uniqueness](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/General/Measure/QuadricDisintegration.lean#L434-L458) · [Rank of the constructed kernel](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/SiegelWeil/OneVector/StandardQuadrics.lean#L142-L151)

**A second, normalization-sensitive test.** The semilocal theorem states $1+|m-1|≤\zeta_R(μ)≤2$ for the finite real lattice mass $m$ at an integral skew target. Substituting our target-four mass would require $257/128≤2$, which fails by $1/128$. The nearby value $255/128$ passes this numerical test; that fact by itself does not identify a fiber measure. The upper-bound contradiction rules out a simultaneous match of all premises, the lattice and the normalization. The trace calculation independently identifies one premise that already fails. Neither argument excludes changing the lattice or rescaling the target Haar measure, operations that would have to be tracked explicitly. [Semilocal lattice-mass theorem](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean#L192-L202)

### A discontinuity that survives constant changes of Haar measure

The regular-locus distinction can be tested on an actual sequence. The old support rule forces the measure at a singular scalar to be zero: the fiber over zero has empty intersection with the locus on which its determinant is a unit. This is already formalized as `SingularZero.rank_one_origin`. The released study also contains `SingularJump.discontinuous`, an explicit failure of continuity of the old lattice-mass function at zero under its hypotheses. The new observation here is how these results test the readable edition's interface. [Old singular member](../ramified-square-dilates/local/SingularZero.lean) · [Old discontinuity theorem](../ramified-square-dilates/local/SingularJump.lean)

For the named ramified example one can see the size of the jump. Fix one admissible family from the simultaneous realization theorem and take $u=1$. In the local field $4^k\to0$ because the uniformizer satisfies $\pi^2=2$ and the valuation of $4^k$ grows as $4k$. In the real numbers the lattice masses $2+2/256^k$ tend to **two**, whereas the assigned zero-target mass is **zero**. The indicator of the compact open coordinate lattice is a continuous, compactly supported nonnegative test. Its fiber integral is exactly this mass. A globally continuous disintegration agreeing on those regular fibers would therefore have to assign lattice mass two at zero, if such an extension with the same normalization exists. This argument determines a necessary value on one test along one sequence; it supplies neither an extension nor a limit along all possible approaches.

Multiplication by any fixed positive finite constant preserves the discrepancy between the zero member and the limiting test integral. Consequently an invertible, continuous target-coordinate change and a constant Haar conversion cannot make the old **entire family** a readable `Place.IsDisintegration` while preserving its values. Restriction to the nonzero locus is the meaningful comparison. This obstruction also applies before imposing integrality or the ideal-zeta bound. [Simultaneous family and all square scales](../ramified-square-dilates/dilates/DilateEndpoint.lean) · [The readable continuity tests](https://github.com/nousentllc/riemann-hypothesis/blob/e063a923620ee7787b4a1270421478645bf66bdb/src/Lib/General/Measure/QuadricDisintegration.lean#L251-L265)

## Next mathematical test

On the analytic side, formalize the signed-average identity using the readable edition's own characters and its `entireL`. The first test with a principal character of nontrivial level should retain the missing Euler factors. This would turn an exact formula relating conventions into a reusable lemma without requiring a common build of both historical trees.

On the measure side, the open comparison is narrower: for a **nonzero target**, explicitly transport the old scalar target Haar measure under $s\mapsto i s$ to the skew line, compute the measure conversion on a single compact open ball, and compare test integrals on the regular locus. The next check is whether the two scalar measures differ by a constant and what it is. The finite-place ideal-zeta bound need not enter that calculation. Changing to a different order would require computing its relation to $B$ and its change in lattice volume.

## Verification record

**Fresh formal replay.** Lean 4.33.1 compiled the original character-family source from the pinned file and the new seven-lemma module. The standalone Lean checker accepted each compiled module. The seven axiom queries returned only `propext`, `Classical.choice` and `Quot.sound`. The run used the archived ramified study objects and compiled Mathlib. Its receipt identifies the compiler, Mathlib commit, original source, imported ramified object and comparison source. [Lean file](InterfaceChecks.lean) · [Replay receipt](lean_receipt.json)

**Earlier evidence used here.** The archived study's receipt covers `SingularZero.rank_one_origin`, `SingularJump.discontinuous` and `RamDilate.original` / `realized`. The present run read those declarations and their receipts. It did not repeat the 108-module study replay. [Archived receipt](../ramified-square-dilates/verification/receipt.json)

**Written and numerical evidence.** The all-modulus signed-average identity, the cross-edition identification at modulus one, and the continuity comparison are written deductions from the cited declarations. The independent finite controls use integer and rational arithmetic and guard against a sign reversal. They can be repeated from the package directory with `python3 -B finite_controls.py`. To repeat the formal check use `python3 -B replay.py`; the five path options select the pinned compiler, Mathlib checkout, compiled original imports, prior study objects, and original source directory. A formal replay requires those dependencies. The ZIP includes both records and the single editable LuaLaTeX file with its logo embedded. [Finite results](finite_results.json) · [Replay program](replay.py)

Justin Candler selected the upstream comparison and provided the pinned intake from the other chat. Uriel/Codex traced the definitions and authored the deductions, controls and supplemental Lean file. This is a component comparison. Independent human mathematical review and an end-to-end replay of the readable RH development lie outside its verification record.
