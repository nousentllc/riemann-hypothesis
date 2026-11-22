# Initial understanding experiments — preregistration

Prepared 2026-11-22, before running this suite. Parent research commit:
`08188ff0c6dd02dfec0bd65d30765862e9db56b7`. Original mathematical source:
`40e56bab026552e089d7afcfeff08d2defb9c005`. No original proof file is changed.

## Evidence classes and decision rule

**N**: independent numerical/exact finite exploration, including synthetic models.
**S**: statement or proof step read in the original pinned Lean source.
**K**: independently elaborated/kernel-checked proof. This suite initially supplies
N and S only. Source text, hashes, regex traces, floating point tests, and Python
assertions never count as K. No numerical outcome proves RH.

All below are mechanism hypotheses, not hypotheses that a finite run verifies RH.
An admissible test failure triggers investigation and is retained in the report;
an expected counterexample to an ablated condition is a successful negative control.
No filtering of parameter failures. Fixed seeds: arithmetic 20261122, cohomology
20261123, covolume 20261124. Float tolerances: relative 1e-10 for algebra,
absolute 1e-9 for inequalities in normalized/log units; exact rational checks
where possible. Grids and criteria are fixed here before measurement.

## H1 — localized Landau criterion

Source: `PoleData`, `WindowHypU`, `landau_window_ineq`, `landau_tails`,
`landau_window`, `landau_growth_contra` in the analytic trace.

N hypotheses/controls:
1. With theta=.5, beta=.75, delta=.5, eta=.05 and U=1,4,16,64,256,
   the minimal majorant for g=+exp(beta*u) has weighted window mass
   `(exp((beta-theta)*(1+delta)*U)-exp((beta-theta)*U))/(beta-theta)`;
   its ratio to exp(eta*U) eventually exceeds one. For g=-exp(beta*u),
   R=0 passes every window but the transform has residue -1. Record both.
2. A delayed positive exponential after u=50 passes early windows and fails
   later ones. A spike strictly between a mesh's sample points defeats a
   point-sampling surrogate; integrating the full spike detects it. Neither
   example refutes the source theorem. Missing an unbounded sequence of
   windows is allowed; losing all late windows is not.
3. For delta=.25,.5,1 and U=1,4,16, use the source's l=2+6/delta,
   sigma=l*(1+delta)*(2+l), k=ceil((1+delta/2)*sigma*U).
   Evaluate gamma-kernel mass and growth-weighted tails in log space, comparing
   them to the explicit source constant C/sigma^k. Control sigma=3 and delta=.5
   should exhibit failure of comparable uniform tail control as U grows.
4. Check the normalized high-derivative identity for signed exponential and
   cosine mixtures against independent quadrature (k=0,4,16; sigma=3; t=0,.7).
   Compare pole/remainder/window rates with d=2.25,r=2.4,E=2.5,c0=M=C=1,
   k=ceil(3.75*U), eta=.5*log(r/d). Their ratio must eventually exceed one.
   d=r is a negative control for the claimed exponential separation.

## H2 — coupled arithmetic budget

Source: `errorBracketSizeWindows`, `proposition_size_bound`, `core_gm`,
`RankVal`, `ErrWindows`, `error_sizes_weak_false`.

Evaluate the normalized three-term bracket from ARITHMETIC.md in logarithms;
factor b out rather than attempt exp(x^epsilon). Use epsilon=.01,.03,.1,
log(x)=10,100,1000; selected-scale representatives n=x^(2+8epsilon),
m=x^(.5-epsilon/16), k=x^(4.5+10epsilon), a/b=x,
dT=x^(-epsilon/8), d2=x^(-epsilon). These are continuous scale models,
not constructed arithmetic groups or a full RankVal witness.

Check each displayed density, m, and k constraint and the constant-absorption
condition 26<=x^(3epsilon/8). Record infeasible rows. For 300 additional seeded
samples per epsilon use admissible m,densities and k between its coupled bounds,
at log(x)=1000. The bound including movement/remainder terms must respect the
source's `1/2+(C+3)epsilon` envelope (C=5) whenever all modeled hypotheses hold.
Check the unnormalized/normalized identity on 200 finite integer-cardinality cases.

Ablate dT, d2 by x^-1, multiply k by x, shrink k to 1, and shrink n by x
separately. Report both constraint rejection and resulting budget growth; never
treat an inadmissible tuple as a source counterexample. Replay the final exact
integer contradiction x^10 > x^5(x+3), x=100000, from the weak-error model.
Also compare amplified residuals with/without the product constraint.

## H3 — finite-exception interval selection

Source: `UpperTheory.V.Win.window1`, `window`, `Good`.
Port the recursive logarithmic construction with exact rational arithmetic.
Independently verify the continuum condition via the forbidden interval
[a,B*a), not by sampling u. Exhaust all subsets of a nine-point adversarial
grid with at most R=4, B=1,2,4 and U=64; add 300 seeded cases R<=8.
Include empty sets, negative/zero a, threshold equality, endpoints, clustering,
and moving exception locations. Expected: every admissible output obeys
U/(2^(R+2)*B^R)<=y, 2y<=U and the whole-window condition.
Omit a harmful exception and understate the cardinality cap as separate controls.
These tests model only the finite-exception selector, not cohomology computation,
finiteness of Sha lengths, or existence of the required number fields.

## H4 — projection, slope, covolume

Source: `GlobalTheory.CutNum.numeric`, `slope_good_ge`, `lcv_le`.
Use 500 seeded rational witnesses of the numeric lemma with all listed
hypotheses checked, including positive total rank and delta<=1/12. Construct
ablation witnesses violating only the discarded-rank, maximum-slope,
lower-total-slope, or denominator envelope, while preserving the weighted cut.

For 2D Euclidean synthetic lattices Z^2, project onto primitive vectors (1,q),
q=1,2,10,100. Compute intersection covolumes from Gram matrices; verify
P^2=P, P^T=P, denominator g=1+q^2, and integral gP. Contrast the projected
image P(L) with L intersect image(P): they are different lattices. Add skew
integer lattices with determinant 1 and a nonorthogonal idempotent control.
Euclidean mu=-2*log(covolume)/rank is a model normalization, not a claim that
these lattices instantiate every arithmetic-number-field hypothesis.
Scan log(x)=1,10,100,1000,10000 for fixed ez=.1,1, A=B=2, C1=C2=1,
using log-domain exponential absorption; include an x-dependent envelope
counterexample. A finite-scale failure before the eventual threshold is allowed.

## H5 — dependency and assumption tracing

Verify all 55 existing SOURCE_TRACE file hashes at the original pin, plus
selected additional interfaces. Produce distinct import and declaration-reference
graphs. Curate references from Main through everyCharacter and selected analytic,
arithmetic, window and covolume declarations. Each curated edge must be witnessed
in its source declaration body, not merely an import or a comment.
Keep unresolved/external edges explicit; do not infer the elaborated dependency
closure or axiom inventory from lexical scans. Mutate a hypothesis token and
inject comment-only dependency bait in in-memory fixtures: guards must detect
the mutation and ignore the bait. Record pinned/current/installed Lean versions,
dependency availability, exact build actions attempted, and no-build reasons.

## Uncertainty ledger before execution

Subjective confidence in finite operational predictions (not formal posteriors):
H1 90–99%, H2 80–95%, H3 95–99%, H4 85–98%, H5 80–95%.
Main risks: faithfully translating normalizations, finite threshold effects,
floating underflow, and lexical graphs being mistaken for elaborated evidence.
Results must state which of these remain unresolved. No probability for RH is
inferred from this suite.
