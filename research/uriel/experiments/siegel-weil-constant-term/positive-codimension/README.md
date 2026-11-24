# How the coefficient one is identified

These two new Mathlib proofs isolate the last comparisons in the positive-codimension mass argument. Both use the input inequalities or limits as hypotheses. Their replay checks what follows from those hypotheses. The original source supplies the automorphic estimates and constructs the tests.

**One vector, ambient rank at least three.** Write $D=[F:\mathbb Q]$. The product of finite local masses is $P(a)$, and the Archimedean test contributes $w>0$. The factorization gives $I(a)=cwP(a)$. For every positive integer $a$, the independent error bound is $|I(a)-wP(a)|\le C a^{DM}$. For arbitrarily large $a$, the lower estimate is $P(a)\ge\kappa a^{D(2M-2)}$ with $\kappa>0$. Dividing on this subsequence leaves $|c-1|w\kappa a^{D(M-2)}\le C$. When $M\ge3$, the residual exponent is positive, forcing $c=1$. The rank condition matters. Take $M=2,D=w=\kappa=C=1,c=2,P(a)=a^2,I(a)=2a^2$. Every growth and error condition then holds. [Pinned one-vector argument, lines 23–101](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/AutomorphicTheory/ThetaDilations/SwOne.lean#L23-L101)

**One vector, anisotropic binary space.** The source obtains two rescaled masses with common limit $V$ and a finite scalar $c$ multiplying one mass into the other. Uniqueness of limits gives $V=cV$. The cancellation applies in the extended nonnegative reals because $0<V<\infty$. Taking $V=0$ or $V=\infty$ with $c=2$ satisfies the equation, illustrating why both endpoint exclusions matter. The control generalizes the source's approach to zero through positive parameters to any nontrivial filter. [Pinned binary comparison, lines 89–145](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountingFormula.lean#L89-L145)

With the pinned Lean SDK and built Mathlib checkout available, run from this directory

```sh
python3 replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT"
```

The script verifies the revisions, compiles both declarations and independently replays their module with Lean's `leanchecker`. The accompanying receipt records the observed axioms, module hash and replay output. It covers these two conditional declarations.
