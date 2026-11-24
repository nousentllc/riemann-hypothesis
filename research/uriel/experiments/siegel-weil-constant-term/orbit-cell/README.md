# The Fourier orbit that cancels

This companion records a kernel replay of a matrix construction used by the original Siegel–Weil proof and an exact example over ℚ(i)/ℚ. All source references refer to commit `40e56bab026552e089d7afcfeff08d2defb9c005`. The [source ledger](../source_trace.json) gives full paths, lines and blob identities.

## Which orbit argument is active?

The stable-range theta lift supplies n≥1 and 2n≤d. In its Siegel–Weil application m=d, so n<m even at d=2n. The branch at `SiegelWeilAtopFieldOf.lean` 52–65 takes the coefficient-one formula. It uses nondegenerate Fourier coefficients, archimedean representation theory and analytic uniqueness. The separate two-orbit constant-term input, `CTSplit_k`, enters the corank induction in m<n. At equality m=n the general formula obtains the multiplier two from a separate equal-rank argument. These are branches within a shared general theorem. [General branch](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/SiegelWeilAtopFieldOf.lean#L52-L65)

For an invertible Fourier index T write a rational coset representative in blocks M=[[A,B],[C,D]]. If det C≠0 its unipotent parameter is C⁻¹D, and its coset belongs to the open Weyl orbit. If det C=0 choose 0≠u in ker C and a vector y with yᵀTu=1. This is possible since T is invertible. With σ the field involution and ε the frame sign, the original construction uses

```
β₁ = u yᵀ − ε σ(y) σ(u)ᵀ.
```

It yields tr(Tβ₁)=2. The conjugated lower-left correction vanishes and the Levi correction is v wᵀ with wᵀv=0. Hence det(I+v wᵀ)=1. An adelic multiple β₀ then fixes the section contribution and gives the character phase −1. The integral of the entire small-orbit sum equals its own negative and vanishes. A summability estimate justifies regrouping. The remaining open-orbit integral is the twisted Whittaker integral. Identifying its continued special value with the theta mass of a Gram fiber uses additional local integral and global mass theorems. [Matrix construction](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/ExistsBetaPf.lean#L7-L66) · [Orbit integration](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnf.lean#L100-L159)

In the other, m<n branch the distinguished row and column of T vanish. There the first orbit yields a lower-rank coefficient. The second gives a section transformed by a partial Weyl intertwining integral. Its dilation character is exp(τ(n−2z)), while the first character is exp(τ(n+2z)). At s₀=(m−n)/2 their weights are 2n−m and m. Distinct weights force a specific regularized residual Fourier coefficient to vanish. The source continues a difference from a right half-plane, allowing it to reach the special point without any assertion that the raw orbit sum converges there. [Two-character conclusion](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/SiegelWeilAstepDeg.lean#L94-L124)

## A calculation by hand

Take n=2, ε=−1, T=[[2,1],[1,1]], A=D=diag(0,1), B=diag(1,0), C=diag(−1,0). These blocks give the partial Weyl element interchanging the first hyperbolic pair. Take u=(0,1) and y=(1,0). Then β₁=[[0,1],[1,0]] and tr(Tβ₁)=2, with field trace 4. Scale β₁ by −1/8 at infinity and zero at all finite places. The resulting conjugated Levi matrix is [[1,0],[−1/8,1]]. Its determinant is one and the standard character at 1/2 equals −1. At T=0 the same translation gives +1. This control exposes precisely why the small-orbit cancellation does not establish the literal constant coefficient by itself. The open-orbit control recovers C⁻¹D=T for the full Weyl element multiplied by n(T). [Exact output](cell_example.json)

## Reproduce the checks

For the example, run `python3 cell_example.py` from this directory with SymPy 1.13.3 installed. It regenerates `cell_example.json` and prints the checked quantities.

For the original kernel leaf, give the portable runner a checkout or archive containing the original `src/`, a Git checkout containing the pinned proof commit, the Lean 4.33.1 SDK, and a built Mathlib checkout at `0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
python3 check_leaf.py --source "$PROOF_TREE" --repo "$PROOF_GIT" \
  --sdk "$LEAN_SDK" --mathlib "$MATHLIB_TREE"
```

The runner authenticates all 38 cited source files, copies the single unmodified leaf into a temporary directory, compiles it, asks Lean to report the theorem’s axioms, and rechecks the emitted module with the separate `leanchecker` executable. The combined ledger is located one directory above this folder. It writes the JSON receipt to standard output, or to a path supplied with `--receipt`. The recorded axioms were `propext`, `Classical.choice` and `Quot.sound`. Imported Mathlib was precompiled. The calculation evaluates matrices and a character phase. The original adelic integrals, global mass formula, full Siegel–Weil identity and RH endpoints were outside this replay. [Kernel receipt](leaf_receipt.json)
