# Can weight 1 be exceptional over the conductor-one slot at 3?

At cutoff $Z=64$, the field $L=\mathbf Q(\zeta_3)$ admits two valid single-center witnesses with exactly the same parameters $R=R'=c=1$. With center $0$ the exceptional set is empty. With center $1$ it is $\{1\}$. The positive and negative answers are for **two specified witnesses of the actual arithmetic bound**. The published theorem later selects a witness by existence. It gives no identity that would pick either answer for its internal set.

| Field and cutoff | Center | Weights in the strict filter | Arithmetic result |
|---|---:|---|---|
| $\mathbf Q(\zeta_3)$, $Z=64$ | $0$ | $\varnothing$ | The bound holds at all 64 positive weights. |
| Same field, cutoff and cap | $1$ | $\{1\}$ | The arithmetic bound at weight 1 still holds. |
| Same field, cutoff and cap | Any chosen $a\in\{1,\ldots,64\}$ | $\{a\}$ | The same argument works for every nominated weight. |

We enumerated all 81 residues against all 64 weights. The direct valuation and congruence implementations agreed on all 5,184 decisions. Exactly 17 residues give the empty set and 64 give a singleton. These counts enumerate the possible residues. No probability law for the proof's choice is assumed. [Complete table and strict-boundary comparison](results/weights.json)

For this field the slot-3 cohomological invariant `shaInv` in the estimate vanishes in every specified layer and every positive weight. Consequently the exceptional set is a sufficient device for proving an estimate. A weight listed in it need not have unusually large cohomology. This conclusion depends on an all-layer class-number theorem. Its mathematical source and its precise place in the formal check are given below.

## What the field contributes

The finite arithmetic calculation yields class number 1 for both $\mathbf Q(\zeta_3)$ and $\mathbf Q(\zeta_9)$. Lean also proves class number 1 and cyclotomic root level $c=1$ directly for the bottom field. For every $n\ge2$, Yokoi's Theorem 3(ii) gives $3\nmid h(\mathbf Q(\zeta_{3^n}))$ because 3 is regular. The pinned field `Fn L Ω 3 n` adjoins precisely these roots of unity. Cubing is therefore bijective on each finite class group. [Finite certificates, independent control and derivation](ARITHMETIC.md) · [Bottom-field Lean proof](BaseField.lean) · [Yokoi, Theorem 3(ii), pp. 416–417](https://www.jstage.jst.go.jp/article/jmath1948/20/1-2/20_1-2_411/_pdf)

The original lemmas `levelRk`, `infRk` and `genOfRk` now give a zero-generator presentation of the tower module `XP 3 L`. Hence it has a single element. The original generator and descent theorems express each layer invariant as a cokernel length on that module, which is zero. This gives both clauses of the original `ABound` with any designated single integral center. Lean identifies the class group cardinality of each source layer with that of the standard cyclotomic field. The remaining input is precisely Yokoi’s all-layer nondivisibility theorem, stated as a premise in the experiment. [Class group transport](CyclotomicTransport.lean) · [Field-specific deduction](RankZero.lean)

## Why both centers are admissible

The published construction obtains a rank cap from Ferrero–Washington, chooses a cyclotomic generator and lifts its action to a matrix on a free module. For each characteristic root it takes a common point of infinitely many closed 3-adic balls. The existence proof uses compactness. It supplies an integral center with a distance inequality. It supplies no numerical residue for that choice. In the final odd-prime window construction, `Classical.choose` also selects a cap, a field model and eventually an exceptional set satisfying the transported estimate. [Detailed source trace, including these separate choices](CENTERS.md)

The two examples can even use **the same generator, presentation and matrix**. The generator itself is supplied by existence. On the zero module its value cannot affect the calculation below. Present the zero module by a free module on one generator. Its zero matrix is an admissible lift. At its single characteristic root $z=0$, each center constraint reduces to $\lVert s-e\rVert_3/81\le1$. Every $s\in\mathbf Z_3$ satisfies it. The next step uses a different inequality, the strict cutoff $\lVert s-e\rVert_3<1/27$. At this cutoff $s\bmod81$ decides the answer for each $1\le e\le64$. For the center 1, weight 28 is exactly at distance $1/27$ and is excluded. [Same-lift proof](ZeroLift.lean) · [Residue equivalence and strict-boundary controls](FORMAL.md)

A prescribed version of the source's `partB` carries the chosen filter into its odd-prime estimate for every qualifying realization of the field. It exposes the equality to the filter at $\lfloor X^{C_t}\rfloor$. All original eventual-scale conditions continue to apply to the estimate. Our calculation at cutoff 64 answers a question about integer membership. [Odd-prime theorem and the original-type recovery](PART_B.md) · [Specialization to this field](SlotApplication.lean)

The common window still combines the sets for slots 2, 3 and 7. The later `CoreAtH` witness inherits an estimate on the selected host. Its statement does not record the individual centers or the exceptional weights. Making slot 3 explicit therefore resolves one input without identifying the full union or producing a numerical host. [Earlier common-window and host trace](../joint-witness/README.md)

## Verification and scope

The computations, hypotheses, positive proofs, rejected substitutions and reproduction commands are recorded in [the protocol](PROTOCOL.md) and [the verification record](REPRODUCE.md). The scoped build used 1,101 original project modules, including 451 compiled for this experiment, and the pinned Mathlib cache. It individually replayed eight original endpoints and nine experiment modules. [Kernel and negative-control records](results/joint_check.json) · [Elaborated proof dependencies](results/proof_terms.json) It does not rebuild the full RH archive. No numerical test of RH is involved.

The next formal experiment is to prove the all-layer class-number input in Lean. A precise first target is the induction step across a cyclic cubic extension with exactly one ramified prime. An executable test of that step must handle arbitrary layers, since checking additional finite class numbers cannot discharge the universal hypothesis.
