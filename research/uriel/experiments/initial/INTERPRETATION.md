# Interpretation, critique, and next experiments

## H1 — localized analytic criterion

The real-pole sign control behaves as predicted. At U=256 the positive-residue
model has log(weighted mass / permitted mass)=84.5862944. The negative-residue
model has zero positive mass on every window despite its pole at beta=.75.
This isolates the need for the positive real-residue assumption in `PoleData`.
It does not imply that residues at nonreal poles must be positive real numbers.

A delayed exponential passes every tested window ending before u=50 and fails
later ones. The between-mesh spike has weighted mass 20 against an allowance
of 1.64872127, although integer sampling sees zero. Finite samples and finitely
many favorable intervals cannot establish the quantified window condition.
Conversely, the theorem does not require every late interval to be favorable:
it asks for a qualifying window beyond every threshold for every positive eta.

The 24 high-derivative quadratures agree with closed-form signed-exponential
and cosine-mixture transforms to maximum relative discrepancy 3.55e-15.
All nine growth-weighted tail tests obey both the Chernoff estimate and the
explicit source constant. For delta=.5 the source chooses sigma=336, with
k=420,1680,6720 at U=1,4,16. The kernel mass inside the first window is
0.9999294504. Values later rounded to 1 are floating-point saturation, not
exact mass-one claims; separately computed log tails remain finite.

Using sigma=3 instead yields log(sigma^k * growth-weighted tail) growing from
4.37942 to 1054.67. A kernel peak inside a window is therefore insufficient by
itself: the outside growth envelope must be included. With d<r the tested pole
to remainder/window ratio has log 61.95698 at U=256; the tied-distance control
d=r has no corresponding separation.

**Critique:** quadrature is checked on explicitly solvable models; no actual
Dirichlet prime statistic or unknown pole configuration is sampled. The high
derivative identity and tail calculations are constituent mechanisms, not a
numerical verification of the universal `landau_window` implication. The suite
does not reproduce complex-pole nearest-center selection or Cauchy remainder
construction. A fixed eta sweep does not establish the source's all-eta claim.

## H2 — arithmetic budget and coupled constraints

All 900 seeded admissible continuous tuples meet the modeled
`1/2+(C+3)epsilon` envelope, with C=5. This is the intermediate `SizeWindows`
bound; it is distinct from the final source `core_gm` exponent 1/2+9epsilon.
Two independent evaluations of the normalized bracket agree in 200 finite
integer-cardinality examples to relative discrepancy at most 4.83e-16.

Only four of nine selected-scale examples meet every modeled condition. The
other five fail `26 <= x^(3epsilon/8)`; three of these also exceed the final
constant-absorbed envelope. These are finite-threshold failures outside the
conditional theorem's modeled domain, not unexplained proof failures.

Each of the five ablations violates a prerequisite and exceeds the envelope.
For epsilon=.03, log(x)=1000, their log(upper budget / target) values are:

| Ablation | Rejected condition | Log ratio |
|---|---|---:|
| dT multiplied by x^-1 | selected-subset density lower bound | 973.2613 |
| d2 multiplied by x^-1 | second density lower bound | 973.2613 |
| k multiplied by x | rank upper bound relative to n | 794.4431 |
| n divided by x | same coupled rank upper bound | 1794.4431 |
| k replaced by 1 | rank lower bound x*m<=k | 938.8181 |

The source weak-error model's final integer comparison gives a ratio
9.99970001e19 at x=100000. Its component residual etaBar=1 satisfies the weak
component bound, whereas the strong amplified-product condition would require
etaBar<=x^-8 in this model. The suite reproduces this final arithmetic
contradiction, not all the formal construction of `modelD` and its hypotheses.

**Critique:** continuous densities/ranks stand in for selected-scale inequalities.
They do not establish integer feasibility, actual finite groups, compatible
theta-lift data, or the other fields of `CoreAtH`. In particular, eps=.1 is a
sensitivity case for the displayed inequalities, not a claim to instantiate
the source's more restrictive full `Scale` record. b cancels from the normalized
bracket; omitting exp(x^epsilon) is algebraic normalization, not dropping its
amplification role elsewhere. The five ablation witnesses demonstrate possible
failure, not that every violation of a sufficient condition must fail.

## H3 — cohomological finite-exception selection

The exact recursive selector and an independently expressed forbidden-interval
oracle agree in all 975 cases: 675 exhaustive subset cases plus 300 seeded cases.
Boundary equality is tested explicitly: the implication is active at u=a,
including the right endpoint 2y. The B=1 grid has eight distinct points because
two prescribed locations coincide; the other grids have nine.

For B=2 and a=3U/8, the naive y=U/2 selection fails, while the recursive choice
y=U/8 passes at U=64,128,1024. An understated cardinality cap is rejected;
omitting the harmful exception makes the proposed whole-window certificate fail.
Nonpositive logarithmic indices and empty sets are harmless in the tested cases.

**Critique:** this verifies a finite rational port of `window1`, whose statement
allows arbitrary real logarithmic indices. It does not compute Sha, its module
length, Iwasawa bounds, exceptional-index cardinality, or field existence.
Nor does it turn the source's bounded obstructions into a vanishing assertion.

## H4 — slope and lattice tests

All 500 rational witnesses satisfy the checked hypotheses and conclusion of
the numeric slope lemma. Four witnesses preserve the weighted cut but violate
exactly one envelope (discarded rank, maximum slope, lower total slope, or
denominator); each violates the conclusion. These are explicit counterexamples
to the corresponding weakened numeric statement.

Twelve synthetic lattice cases use projections onto (1,q), q=1,2,10,100,
under three unimodular bases. The integral denominator g=1+q^2 is verified.
The retained intersection has covolume sqrt(g), while the projected image has
covolume 1/sqrt(g). Substituting one for the other reverses the slope effect.
With mu=-2 log(covolume)/rank, the retained slope is -log(g), so the
denominator-free cut fails for every tested q. At q=100 these covolumes are
approximately 100.005 and .00999950, and the retained slope is -9.21044037.
An idempotent nonorthogonal projection has Pythagorean residual -8.

Fixed-envelope exponential absorption fails at log(x)=100 for ez=.1
(log loss/E about 199.0053), then passes at log(x)=1000. It passes sooner
in the sampled grid for ez=1. If Q/E is allowed to depend on x as
exp(2*x^(ez/7)), the loss grows instead. The order of fixed constants and the
eventual threshold is substantive.

**Critique:** the lattice tests use a Euclidean analogue with an explicit
normalization. They do not instantiate a totally complex number field, all
embedding norms, arithmetic slope maxima, or the full `slope_good_ge` setting.
The 2D lattice controls also do not satisfy the small-bad-rank hypothesis of
the downstream 12*delta*Q lemma; that lemma is tested separately by rational
witnesses. The source-derived link to `lcv_le` remains conditional on its
geometric inputs.

## H5 — source graph and verification limits

All 55 prior SOURCE_TRACE hashes match the original pin. Ten additional
interfaces bring the inspected machine-readable corpus to 65 files. All 42
curated body references across 26 declaration nodes are witnessed. The separate
import graph has 529 occurrences, 76 resolved inside this selected corpus and
453 unresolved here. This is a partial map, not a statement of complete proof
dependence; unresolved imports are not missing theorems in the archive.

The small lexer masks nested comments and strings. It rejects comment/import-only
bait and catches mutations of six selected hypothesis fragments by their
occurrence counts. It does not elaborate Lean, resolve all namespaces, inspect
generated declarations or implicit/typeclass dependencies, or compute axioms.
Its lexical name `ih` denotes a local induction hypothesis, not a global theorem.

Full Lean build is infeasible within this lightweight run without installing the
pinned toolchain, retrieving dependencies and the full archive, and allocating
substantially more build resources. No build or kernel replay was attempted;
there is no local formal-proof verdict. The current [MIT external record](https://math.mit.edu/~drew/grh/)
was checked separately and reports completed compilation/module replay and
independent checking at its stated pin. Those reported checks are not ours.

## Harness failures and protocol deviations

1. System Python 3.13/SciPy 1.15.2 could not load a native library. Execution
   stopped before experiments. The complete error is retained. Python 3.12.9
   with NumPy 2.2.4/SciPy 1.18.0 worked; requirements record the executed versions.
2. The first full run had two failing tests: an unjustified >1000 case-count
   assertion and two unqualified source-reference spellings. The grids were
   not changed. The count was replaced with its combinatorial total; references
   were replaced with the exact `_root_`-qualified source names.
3. The second run exposed a mutation-guard weakness: the RankVal exponent
   fragment occurs twice, so deleting one still leaves a present token. The
   guard now compares occurrence counts. This is an improvement to the audit
   harness, not a mathematical finding. Both runs remain in `runs/`.
4. Final regression outcome: 25 tests passed. No parameter grids, tolerances,
   mechanism hypotheses, or expected mathematical controls were tuned after
   looking at their outcomes. Published commit metadata differs from local Git
   metadata; publication compares tree hashes and retains the preregistration
   and failed-run history.

## Uncertainty ledger and next experiments

The finite observations support H1–H4 in their stated model domains; H5 now
passes its syntactic tests after the documented repairs. Subjective confidence
in faithful finite-model implementation is roughly 90–99% for H1–H4 and 80–95%
for H5's partial trace, not a statistically calibrated posterior. These bands
do not measure RH or the full archive. Main remaining uncertainties are source
normalization outside these models, actual arithmetic existence, and elaborated
dependencies. The stronger hypothesis “these tests independently validate the
full proof” is unsupported.

Next experiments, in priority order:

1. **Analytic:** implement two nearby conjugate-pole models, vertical-center tie
   avoidance, and an explicitly bounded analytic remainder. Test the combined
   norm-plus-real-part inequality directly with high-precision or interval
   arithmetic. Preregister d/r margins and tail-error budgets first.
2. **Arithmetic/cohomology:** trace the existence constructions discharging
   `CoreAtH` and the finite-exception cardinality bound; separate their record
   fields into an assumption matrix. Add integer-feasibility checks using the
   full `Scale` restrictions. Do not infer those objects from continuous tuples.
3. **Formal:** provision an isolated original-pin Lean v4.33.1 environment,
   obtain its Mathlib pin, and export elaborated dependency/axiom information
   for selected declarations before scaling to a full build. Only such a run
   can replace the present lexical graph with kernel-level evidence.
