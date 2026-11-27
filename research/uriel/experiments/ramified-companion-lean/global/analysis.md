# Exceptional primes and global growth

Fix the CM extension, nonsingular Hermitian matrix of rank M at least three, standard coordinate Haar data, a nonzero global scalar β and an admissible original Gram family. For the prime-block criterion assume that its measure at β is nonzero at each finite place. Let s₀=N²β, h=2M−2, D=[F:ℚ], and let u(v,s) denote the real mass of the undilated coordinate lattice at target s. The kernel-checked criterion selects one positive N and one finite B before testing any floors.

## Exact criterion

Let p(v) be the positive rational prime under v. For each p in the image of B set C(p,k) equal to the product of u(v,p^(2k)s₀) over B above p. Then the existence of a single positive coefficient in P(Nt)≥c(Nt)^(Dh) for all positive integers t is equivalent to a positive eventual lower bound on every sequence k↦C(p,k). The upper and lower comparison constants in the proof depend on B and the summable majorant, independently of t. Fixing the exponent and multipliers is essential.

The equivalence uses the algebraic identity P(a)=a^(Dh) times the product of u(v,a²β) for every positive a. Its original ingredients are exact valuation scaling, finite support of ideal principal norms, and convergence for the nonzero target. The almost-all-place estimate bounds the exterior product above and below uniformly, since all moving targets are integral and the bound 2/q² is summable and at most one half. The unit part of t has exact valuation zero at v and preserves the lattice. Its square can be removed from the argument of u by the original scaling law. As a result, all exceptional places above a rational prime share one index k. Distinct rational-prime indices can be prescribed independently.

Taking t=p^k freezes all other rational-prime blocks at their positive initial masses. The upper exterior comparison therefore propagates any global floor back to this block. For the reverse implication a finite initial part of each block sequence is positive by the previously verified bounded-order lower inequality. Its minimum and an eventual floor give a lower bound for all k. The product of the block floors times the lower exterior constant works on every positive integer multiplier. The case of an empty exceptional set follows with the empty product.

## Local geometric interface

A positive lower bound in a punctured neighborhood of zero at the exceptional places suffices. The original scalar arguments p^(2k)s₀ tend to zero locally and remain nonzero. A finite intersection of eventual bounds gives the p-block threshold. This keeps the same N and never evaluates the singular member. If punctured floors are available at every place, the original hne premise follows separately for every nonzero β. Choose k deep enough that the dilated scalar has positive lattice mass. The exact scaling identity at the same k gives positive mass for the β-fiber on an enlarged lattice. The choice of k may vary with the place.

The fixed multiplier N serves a separate arithmetic purpose. For the six-square form and β=1/2 a rational solution exists, but an odd dilation cannot be represented integrally even modulo 2 after clearing the denominator. This excludes an inference about all sufficiently large integers from a result on all multiples of N.

## Adversarial controls

The exact-rational runner uses four synthetic input families. It checked the block identities across t=1,…,4096 and all single-prime directions through shell 24. Two factors 2^(−k), 2^k assigned to the same prime keep their product one. Placed at different primes 2,3 they still give one on t=6^k, but the product falls to 1/16,777,216 at 2^24. The late-decay sequence 1/max(1,k−11) passes the proposed floor one at all 4,096 sequential integers and equals 1/13 at 2^24. The fourth control feeds the dyadic conjectured formula through block aggregation; this checks propagation only. The independent counts and formal fiber calculation are on the dyadic track.

Compensation is a phenomenon in the abstract control family. An individual positive floor follows from a block floor if the other constituents are separately uniformly bounded above. No example here exhibits compensation in a genuine Hermitian family.

## Verification

The Lean modules use the original measure and dilation types. The source hashes and declaration anchors in anchors.json were compared to the original pinned Git tree. The files PrimeBlocks, GrowthSandwich, ExceptionalPrimeCriterion, NeighborhoodGrowth, GermSupport, BlockIdentification, and DenominatorControl compiled and individually replayed in Lean 4.33.1. The only transitive axioms printed for their audited declarations were propext, Classical.choice and Quot.sound. This audit of selected statements used earlier original and Mathlib objects. It did not build the entire RH source tree from scratch. Run controls.py to regenerate controls.json exactly. The single paper develops the equations and arguments in full.

## Sharp support and the joined theorem

UncappedGrowth.all_multiples joins the verified pointwise local theorem directly to the global comparison, including the deduction of hne. OptimalSupport.positive_iff_multiple gives a stronger answer. For fixed β≠0 there is a positive, uniquely determined N and one c>0 such that P(t)>0 exactly when N divides t, with the polynomial lower bound on every such t. Outside this support the Euler product is nonnegative and has an exact vanishing factor.

To construct the characterization, enlarge B by the finitely many places where β is not a local unit. At v in B, the shell f(k) at p(v)^(2k)β is positive eventually by the local chart. Exact scaling and lattice inclusion show that positivity at one shell implies positivity at its successor. Its positive support is consequently the terminal interval starting at the least positive shell j(v). The local masses have a positive lower bound on that whole interval. The least common multiple of p(v)^j(v) over B gives N. The global upper comparison proves vanishing when divisibility fails. Repeated places over one rational prime contribute the largest required exponent. The support runner's three synthetic thresholds 2¹, 2² and 3¹ produced exactly 341 positive dilations among the first 4096 integers with generator 12.

This gives an existence and uniqueness theorem for a numerical generator. It does not extract its value or an effective search bound for general inputs. The test family β=1/2 proves the obstruction at every odd dilation. The separately checked LocalRegularSupport.all_local_targets proves that a punctured germ implies positive measure of some integer dilation for every nonzero local scalar, even outside the embedded global number field. The extra support modules, the integrated result and the sharp classification compiled and independently replayed. The per-module hashes and emitted checker lines are recorded in receipt.json.
