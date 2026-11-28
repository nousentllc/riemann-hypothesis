# Which odd slots remain for the primitive character of conductor one?

The exact set is **{3, 7}**. Three factors in the source product reduce to one. The other two factors are ordinary primes. The nontrivial arithmetic input is the class number of the splitting field of X²+7.

## Source identities

These paths are relative to `src/` in pinned commit `40e56ba`.

| Declaration | File | Lines | Specialization |
|---|---|---:|---|
| `PChar.one` | Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean | 19 | conductor 1 and character 1 |
| `Kstar` | Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean | 50 | the splitting field of X²+7 once pK=7 |
| `ordC, pK, hStar, pOne, Bchi` | Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean | 57–67 | 1,7,1,3, and the set {3,7}, respectively |
| `Lchi` | Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean | 71 | slot l has field descriptor AbF.cyc l, the full cyclotomic descriptor |

The least prime congruent to 3 modulo 4 and at least 7, coprime to 1, is 7. In the second minimum the congruence is modulo 1. The prime 2 fails coprimality with 14 and 3 passes. Hence pOne is 3. The product whose odd prime factors enter Bchi is 1·1·7·1·3=21. Inserting 3 again has no effect.

## A short arithmetic proof of the class number

The field cut out by X²+7 is K=Q(√−7), since −7 has no rational square root and the second root is the negative of the first. Write ω=(1+√−7)/2. The ring of integers is Z[ω]. Indeed, if z is integral, its trace t and norm n are integers. Write z=(t+u√−7)/2 with u rational. The identity 7u²=4n−t² forces the reduced denominator of u to have its square dividing 7, hence u is integral. Since t²+7u² is divisible by 4, t and u have the same parity. Therefore z=(t−u)/2+uω. Conversely ω satisfies the monic equation ω²−ω+2=0 and all elements of Z[ω] are integral.

For every complex z choose k integral to make its imaginary coordinate differ from that of kω by at most √7/4. Then choose j integral to make the real part of z−kω−j have absolute value at most 1/2. The squared distance to j+kω is at most 1/4+7/16=11/16<1. Applied to z=a/b for nonzero b in the ring of integers, this produces q=j+kω and remainder a−bq of absolute norm strictly less than the absolute norm of b. The norm is a positive integer on nonzero algebraic integers. Euclidean division therefore makes every nonzero ideal principal, by selecting an element of smallest positive norm. Its class group is trivial. Class number is invariant under a field isomorphism, so hStar(PChar.one)=1.

## What this decides for the gap

At conductor one the remaining odd slot beyond 3 is **7**, and its cyclotomic descriptor corresponds to Q(ζ₇). The imaginary quadratic field used to obtain hStar enters the roster calculation. The slot-7 descriptor uses the full seventh cyclotomic field. A finite roster reduces the number of simultaneous restrictions. It supplies neither slot's obstruction centers, support equality across choices, nor a size-independent bound for a prescribed gap.

The class number step above is a written proof. The small Lean module makes its as-yet unformalized specialization explicit as a hypothesis of the roster equality. The finite Python check independently verifies the two minima, norm-square rounding bound and final factorization. Its rational bound concerns the displayed rounding argument, and it does not compute ideals or instantiate a set of cohomological centers.

## Replay and search boundary

Run `python3 check.py` for the arithmetic receipt. With a Lean 4.33.1 toolchain, the pinned Mathlib Git checkout with built dependencies, a checkout or export of the original proof, and its compiled objects, run the following (the original import root contains Development/ and Formalism/):

```sh
python3 replay.py --toolchain "$LEAN_TOOLCHAIN_DIR" --mathlib "$MATHLIB_DIR" \
  --source "$ORIGINAL_SRC" --proof-lib "$ORIGINAL_OLEANS"
```

Additional `--proof-lib` arguments can supply complementary compiled object roots. The replay validates three original source files against `source.json`, the Mathlib revision, and the Lean version. It builds in a fresh temporary directory, requires all six axiom reports to use only propext, Classical.choice and Quot.sound, then invokes leanchecker on the new module. It relies on available compiled imports. The two reports are `results.json` and `kernel.json`.

A targeted search for a class-number/PID specialization for discriminant −7 in the pinned Mathlib number theory sources and the retrieved original source tree found no ready-made declaration. Mathlib's `Mathlib/NumberTheory/NumberField/ClassNumber.lean` provides `NumberField.classNumber_eq_one_iff` and general Minkowski-bound criteria. Applying either route still requires an explicit ring-of-integers identification or sufficient concrete field discriminant/bound data. The exact seven-membership theorem only uses positivity of class number and has no class-number-one premise.
