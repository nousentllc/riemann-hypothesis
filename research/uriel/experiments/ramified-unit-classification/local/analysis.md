# Regular fibers at a singular limit

## Question and gain

For a given finite place, basis lattice and admissible original Gram family, can all sufficiently small nonzero scalar targets share a positive lower mass? The global growth argument needs the quantifiers in this order. Separate positive witnesses at arbitrarily many targets would leave the infimum undetermined. The source has two usable structures in distinct parts of the archive. Its five-variable theorem supplies nonzero isotropy at every completion. Its rank-one set formula turns an inequality on Haar tubes into a pointwise inequality for the original measure at each nonzero target.

## From the pinned statements to local geometry

The CM trace-basis theorem produces a symmetric, invertible matrix over the totally real base. It represents the full two-vector pairing after base change, including the case where the tensor algebra splits. A Hermitian rank of at least three gives at least six scalar coordinates. The theorem for five variables applies after diagonalizing this trace form over the completion. Transport through the isometry yields a nonzero vector e with eᵀBe = 0. Invertibility of B separately yields Be ≠ 0. These two conclusions play different roles. The archive's rank-one Gram-entry identity lifts the trace zero to the actual Gram-matrix entry, and the coordinate-basis surjection lifts e to an actual tuple.

There is arithmetic content behind five. Under an assumption of anisotropy, the pinned proof picks an invertible matrix minimizing a discrete valuation expression formed from the quadratic values of the basis and its determinant. Three of five exponents share parity. Scaling their coordinates produces a ternary integral quadratic polynomial admitting a primitive zero modulo the maximal ideal, by the finite-field degree-versus-variable-count argument. Such a combination has value contradicting the extremal-basis inequality. The square-lifting ingredient requires |u−1| < |4|. At a dyadic place this is a consequential restriction. The proof does not lift a general residue-field zero by claiming its derivative is a unit.

With Q(x)=xᵀBx/2 put z = (Be)ⱼ⁻¹ eⱼ at a nonzero coordinate of Be. Then b(z,e)=1 for b(x,y)=xᵀBy. Subtract Q(z)e, giving f with Q(f)=0 and b(f,e)=1. This works because Q(w+y e)=Q(w)+y b(w,e). Clearing denominators of e and f separately gives integral e′ and f′ with Q(f′)=0 and b(f′,e′)=δ ≠ 0. The derivative may have strictly positive valuation. A lattice-independent unit assumption would be too strong.

## Measuring the actual patch

The companion translation-averaging theorem uses the target ball D=δO. On a sufficiently small open W near f′, the slope b(x,e′)/δ is a unit and Q(x)∈D. For fixed x∈W and y drawn from Haar probability on O, Q(x+y e′) is uniform on D. Translation by y e′ preserves the full coordinate Haar measure and the integrality constraints when x and y start integral. Fubini therefore gives original product-coordinate tube mass ≥μ(W)λ(V)/λ(D) for every measurable V⊂D. This expression requires neither choosing a complement to the hyperbolic plane nor explicitly computing a determinant for a lattice-basis change.

The source map from an original tuple to its basis coordinates pushes coordW to the specified product of Haar measures, identifies latV with integrality of every coordinate, and identifies the target half trace with Q. FloorTransfer proves equality of the two tested tube volumes via preimages. A small open target test inside each neighborhood of s can be chosen with finite positive Haar measure using compact local neighborhoods. The original pointwise ratio formula applies at s ≠ 0. If m(s)(L) were smaller than c, take half the gap as the error tolerance. Applied to this positive-mass test, its upper bound contradicts the transferred lower test.

## Controls and failure modes

The finite-ring bijection and the normalized affine Haar identity in LocalChart independently validate the unit-slope mechanism. Across thirteen rings and 401 target–modulus pairs, each of two unit-slope forms contributed exactly |R×||R| vectors per target. The exhaustive run examined 2,092,816 triples per polynomial. Multiplying both the slope and the offset by p killed all targets outside pR and gave p times the original count on that ideal. The two-square form at p=3 supplied zero representatives for target three modulo 27, 81 and 243, while targets one and nine had positive counts. This control concerns all small target classes. Its valuation-one obstruction alone says nothing adverse about square dilates of a single square target.

A separate kernel theorem gives m(S)=0 whenever det S is a nonunit. In particular m(0)=0. The proof is the support conjunct of IsFibreFamily. A local chart can give positive normalized tube mass at zero even when the actual singular member there has measure zero. The distinction is forced by the definition.

## Existence and reproducibility

The rank criterion and quantified local bound give exact implications. They do not print coordinates of e or f, a computable valuation threshold, or the constant c. The choices of a diagonalization, a zero of the five-variable form, a compact neighborhood, and a positive Haar mass all enter. The numerical checks have rational finite outputs and test these mechanisms in independent models. The original proof commit is 40e56bab026552e089d7afcfeff08d2defb9c005. The accompanying trace gives verified source blobs and declaration line numbers. The paper and top-level verifier describe the Lean imports and checked endpoint.

## A radius cannot be uniform in the form

Fix the Gaussian rank-three lattice at two and scale its identity matrix by 2^H, H≥1. Every integral Gram scalar is in 2^H Z₂, so its slice at the nonzero scalar 2^(H−1) is empty. The original support condition forces zero mass there. These failing targets tend to zero as H grows, ruling out any neighborhood that works uniformly for every form in this family. This is a written support argument. The fixed-form theorem is compatible with the image ideal shrinking as H grows.
