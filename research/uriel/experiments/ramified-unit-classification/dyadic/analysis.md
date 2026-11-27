# The exact local floor for integer square dilates at two

At the dyadic place of **Q**, use the identity Hermitian form in three Gaussian variables, ordered integral basis `(1,i)`, integral coordinate lattice, and target-one normalization. For every admissible original family, every integer multiplier `t>0` has fiber mass

```
m(t²)(L) = 1 − 1/(4·16ᵏ),    k = ord₂(t).
```

The minimum is **3/4** and the odd multipliers attain it. At even multipliers the minimum is **63/64**, attained when exactly one factor of two divides the multiplier. The existence theorem produces one measure and one family satisfying the entire infinite list simultaneously. For the same family, its assigned member at zero is the zero measure. The normalized ambient zero-centered tubes have density one at every depth.

## Reconstructing the computation

The trace of the identity Hermitian form becomes twice the six-coordinate dot product. The factor of one half in the original scalar coordinate cancels this two. With each scalar integer ring assigned mass one, a residue box modulo `m=2^r` has ambient mass `m^-6`. The target ball has mass `m^-1`. Thus `N_r(b)/m^5` is the normalized tube density.

For a target divisible by four and depth at least two, a primitive tuple has exactly four odd entries. For each of the fifteen choices of odd positions, fix one odd position as the pivot. At depth two that parity pattern has 64 solutions. At depth three and above, exactly half of the remaining five-coordinate choices of prescribed parities leave residual 1 modulo eight. Adding two to an exposed even coordinate interchanges the two possible even square residues. Every residual 1 modulo eight has precisely four odd square roots. A single parity pattern therefore contributes `m^5/16` at each depth at least two. Summing gives primitive density 15/16 for **every** target in four times the integer ring.

The Lean proof computes the same constant by a first-odd-coordinate decomposition that works in all dimensions. If the first coordinate is even, the tail must be primitive. If the first coordinate is odd, an arbitrary tail contributes whenever it leaves residual 1 modulo eight, with four choices of the first coordinate. Reduction modulo eight has constant tuple fiber sizes. The primitive contribution in dimension d at depth `r=3+h` equals its base-eight count times `(2^h)^(d-1)`. At dimension six the two eligible base-eight residues 0 and 4 each have 30,720 primitive solutions.

Every all-even vector has form `x=2y`. At modulus `4m`, the halved vector lies modulo `2m`, with its equation specified modulo `m`. Each solution modulo `m` supplies 64 choices. The exact recurrence is

```
N_(r+2)(4b) = (15/16)·2^(5(r+2)) + 64·N_r(b)
A_(r+2)(4b) = 15/16 + A_r(b)/16,  A_r(b)=N_r(b)/2^(5r).
```

An odd multiplier permutes all coordinates at every depth. Target-one density is one at depths 0 and 1 and 3/4 at depth 2 and later. Iterating the recurrence gives `A_r(t²)=1` for `r<2k+2` and the stated final value thereafter. In particular the last coarse tube always gives a strictly different number. At k=2 the last shallow density is 1 at depth 5 and the first exact mass is 1023/1024 at depth 6.

For each positive integer target the cylinder sets of sufficiently high depth form a neighborhood basis inside the nonzero regular target locus. Disintegration and continuity on that locus identify the value at the center from the equality of tube integrals on arbitrarily small positive-volume compact sets. The realization and the finite-to-continuum bridge are in [GaussianDilates.lean](GaussianDilates.lean). The universal lower bound is [GaussianSharp.lean](GaussianSharp.lean). The zero-center assignment uses the first support condition in the original definition, which holds for every center. The preimage of zero intersected with the source locus of unit Gram determinant is empty. Consequently the family assigns zero to the whole source at that center. [SingularGaussian.lean](SingularGaussian.lean)

## Checks and provenance

The independent Python observation contains 2,047 residue bins, 511 primitive-plus-even comparisons at all multiples of four in moduli 4 through 1,024, 2,816 comparisons of square targets, and literal enumeration of the 266,305 six-tuples over moduli 1, 2, 4 and 8. All comparisons passed. Numerical coverage ends at modulus 1,024. Universal quantifiers come from the separate Lean theorems. A four-square control loses its primitive vectors at zero modulo eight, because four odd squares sum to four modulo eight. The rank-three floor depends on the representation and dimension. These figures alone do not supply floors at other exceptional places. [Recorded exact results](results.json)

The original study fixes Lean 4.33.1, Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, and the published original source 40e56bab026552e089d7afcfeff08d2defb9c005. The predecessor study provides its source manifest, compact-test contact, measure normalization and nonvacuity. The present modules are additive research results. [Original Gram-family definition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/CompanionTheory/SpectralGeometry/CountingDefinitions/AdelicEulerProducts/IsEulerProd.lean#L61-L65) · [Original support and disintegration](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GenusMassVolumes.lean#L183-L189) · [Predecessor source manifest and replay](https://github.com/nousentllc/riemann-hypothesis/tree/b4d12e0825d2191f38fdfb5e97b327c8c8ad1b3d/research/uriel/experiments/gaussian-target-four)

From this directory, run `python3 -B experiment.py` and compare its JSON to the archived results. For a full local recreation from the predecessor sources run the following with the pinned and built Mathlib and Lean roots. The runner checks the version, commit, and every predecessor source hash, then compiles the old and new modules, kernel-replays each new module, and audits sixteen named declarations for their axioms. Repeated `--imports` arguments select existing predecessor object roots. The receipt was produced in that mode, with freshly built new modules.

```sh
python3 -B replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" \
  --prior ../../gaussian-target-four
```

A written corollary covers every nonzero integral target b. If b=2^v w with w odd, the final density is 1 minus the quadratic character of w modulo four times 4^(-v-1). The density is initially 1 and stabilizes exactly at r=v+2. With no factor of four, the primitive modulus-eight counts for residue classes 1 and 5, 3 and 7, 2, and 6 yield base densities 3/4, 5/4, 15/16 and 17/16 respectively. All-even count is zero in those cases. The same descent handles each remaining factor of four. The independent code verifies this prediction in every one of its 2,047 residue bins, with 2,026 resolved nonzero bins, ten unresolved nonzero bins and eleven zero bins. The released all-depth and original-family endpoints formally specialize to the square-dilate family.
