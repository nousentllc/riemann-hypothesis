# Where to take the proof and memory experiments next

> **Archive navigation.** References to files outside this Git branch are shown as local source paths or labeled as unavailable here. The [original snapshot](https://github.com/nousentllc/riemann-hypothesis/tree/248c8f4838155354c024a6224690245067edb102/research/uriel/portfolio/publication-archive) retains the original link markup.

22 November 2026. Local assessment following the [slot-3 report](../slot-three-paper/Slot_Three_Witness_Experiment.pdf). The source is pinned at `40e56bab026552e089d7afcfeff08d2defb9c005`, with earlier experiments at `e674cb750ef96b2f5e7cd46586ea4edb9998715a`. The new checks below are exploratory. They are outside the earlier preregistrations.

## The decision

Make the production of a prime-sum bound on the selected arithmetic host the primary proof question. The source already proves the implication, and earlier builds reached the comparison and zero-free wrappers. Our research question is how the conditions that supply the estimate survive on the same mathematical object, at the required scales, with uniform losses. The fixed-center, changing-cutoff question gives the memory project a related test of what a record actually identifies.

| Area | Established locally | Remaining question that changes the picture |
|---|---|---|
| Analytic windows | The original 30-module localized-Landau implication was replayed. One conductor-one window also has an independent finite maximum enclosure. | Which arithmetic inputs supply an estimate throughout arbitrarily late whole windows? |
| Arithmetic witnesses | The prime row and cohomological estimate can be followed to the same core index. At slot 3, a single generator and presentation support every named integer label, and the layer invariant vanishes. | Where do the retained-set proportions, character bounds and uniform constants enter for that host? The source chooses its own witness. |
| Covolumes | The existing scalar extremal example requires the coefficient 12 from the displayed scalar assumptions. | Can the extremal case be realized by the geometric inputs? |
| Memory | At one cutoff the exact number of answer profiles is known. Under the earlier 27-value budget the optimum at the stated coverage is eleven licensed positives. | How much remains recoverable when the reader asks a different question of the same stored witness, and can a learned reader use the available information? |

[Analytic experiments](https://github.com/nousentllc/riemann-hypothesis/tree/b616d08a805e05e358ad0d2b3cd7b180e058a19e/research/uriel/experiments/second/README.md) · [Finite covolume result](https://github.com/nousentllc/riemann-hypothesis/tree/b616d08a805e05e358ad0d2b3cd7b180e058a19e/research/uriel/experiments/second/NUMERICAL.md) · [Prime-row and core trace](https://github.com/nousentllc/riemann-hypothesis/tree/bafda6a5728eb08b601943f0c9cb1d38d27c03a9/research/uriel/experiments/joint-witness/README.md) · [Arithmetic endpoint](https://github.com/nousentllc/riemann-hypothesis/tree/e674cb750ef96b2f5e7cd46586ea4edb9998715a/research/uriel/experiments/ascent-witness/SharedLift.lean)

## The handoff worth opening

The source's `EFamC` supplies explicit-formula conditions for **every** host index beyond a threshold. The core comparison selects **one** index. Taking the maximum of three thresholds permits both estimates to be applied to that same host, its actual retained set, and the same scale. The explicit-formula input `EAtH` includes retained character data, a quantitative coset-share condition on that set, pointwise character bounds and a logarithmic-derivative bound. The constructor `PreRows.eAtH` explicitly requests both host conditions and the share bound. Knowing only the number of retained elements need not identify how they are distributed among cosets.

The direct assembly uses losses $e_D=2$, $e_L=0$, yielding $x^{1/2+9\varepsilon}$. They are fixed before choosing the tolerance. We kernel-checked a misuse of the quantifier order. If $e_D=1/(2\varepsilon)$ can be chosen afterwards, even $g(x)=x$ satisfies the weakened upper bound at every $x\ge1$. Yet it violates $g(x)\le x^{3/4}$ on every interval starting at 2 or later. This is a generic function constructed to distinguish two statements. The original theorem uses the stronger order.

**Next experiment.** Trace the origins of the retained-set shares and the bounded-character logarithmic derivative into the same `EAtH` object consumed by `core_gm`. Keep the host, retained set, family index and scale visible in an extracted theorem. Accept the actual source composition. Test a weakened summary using independent host indices and a surrogate preserving cardinality alone. For each rejection, distinguish a genuine mathematical counterexample from a mere Lean type mismatch. Success means identifying the supplying declaration and its exact hypotheses for each of those inputs and explaining how its constants depend on the family and the tolerance.

[All-index quantifier](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopDefs.lean#L13-L16) · [Selection of the same host](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L17-L25) · [Share and character inputs](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L129-L138) · [Assembly constants](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L50-L54) · [Quantifier control](Uniformity.lean)

## A corpus finding that changed the arithmetic assessment

Boyd and Vandenberghe, *Convex Optimization*, §§4.5.2–4.5.3, printed pp. 161–163, explain how positive sums of monomials become convex objectives after taking logs. The earlier normalized error budget has precisely that form in its positive rank variables when the scale and densities are held fixed. This suggested asking which density failures can be repaired by changing ranks. The following bounds are deductions for our scalar budget. The textbook supplies the method. **Local textbook** (local source; not included in this repository)

Write $L=x^\varepsilon$, let $d_T,d_2$ be the two positive retained fractions, and use the earlier normalization $a_E/b=x$. Its bracket $S$ contains the positive terms $2x/(m d_2)$ and $4mL/(d_Td_2)$. Their product is independent of $m$. The arithmetic–geometric mean inequality and the positive additive error in the full scalar budget give the necessary condition

$$
L^5 S+4/(x d_2)\le\sqrt{x}(L^8-4L)
\quad\Longrightarrow\quad
d_T d_2^2 (L^8-4L)^2>32L^{11}.
$$

At the archived $x=2^{1024}$, $L=2^{16}$ row the retained fractions are $d_T=1/8$ and $d_2=2^{-16}$. Dividing either fraction by $x$ violates the necessary condition for **all positive ranks** $m,k$. The earlier experiment had established failure at the sampled ranks. In the opposite direction, keeping the archived ranks and $d_2$ fixed, changing $d_T$ from $1/8$ to $1/16{,}384$ still satisfies the full scalar envelope. Changing it to $1/32{,}768$ fails. The exact transition lies between those values. The script verified the last failing and first passing integer subset counts. A thinner scalar row can violate the separate host-density hypothesis even when its budget passes. Thus one can measure the difference between what this inequality consumes and what the joint construction must supply. [Exact integer comparisons](check_density.py) · [Real-valued necessary condition](DensityGate.lean) · [Earlier normalized budget](https://github.com/nousentllc/riemann-hypothesis/tree/b616d08a805e05e358ad0d2b3cd7b180e058a19e/research/uriel/experiments/second/arithmetic.py)

A second, limited comparison comes from Naomi Sweeting's *On the Bloch–Kato conjecture for some four-dimensional symplectic Galois representations*, §9.1, Lemma 9.1.2, p. 113. One Frobenius conjugacy condition supplies both an admissibility property and a cohomological localization property for the same primes. It is a useful example of how a joint requirement can be proved. Its hypotheses and infinitude conclusion supply neither the prime boxes nor the uniform character estimates in this formalization. The local search used extracted text of 87 standalone mathematics PDFs and six combined volumes. Repeated papers counted as one source, and unsearchable scans limit coverage. **Local paper** (local archive path: `../../sources/On the Bloch-Kato conjecture for some four-dimensional symplectic Galois representations.pdf`)

## Keep slot 7 as a test of generality

The conductor-one odd slot at 7 gives $\mathbb Q(\zeta_7)$. We formalized its classical class-number-one base case in pinned Lean. The Minkowski bound is below 5. Prime ideals above 2 and 3 have norms 8 and 729, respectively, which excludes every possible nontrivial class under that bound. PARI/GP 2.19.1 independently returned class number 1, discriminant −16,807, and full certification. To reproduce in GP, evaluate `b=bnfinit(polcyclo(7),1)` and then `[b.no,b.disc,bnfcertify(b)]`. The all-layer slot-7 ascent, cap-one admissibility and the selection of a witness are further steps. The most informative use of slot 7 would be to specialize a common **prime-degree** ascent lemma at both 3 and 7. The two-primary field also depends on the selected ordered primes and requires different work. [Base-field Lean proof](SevenBase.lean)

## Changing the query on a fixed stored center

The earlier memory census concerned any weight at **one known cutoff**. If the same integral center is kept and a future reader may ask about any cutoff through $T$, then two witnesses with the same terminal exception list can have different histories. At $T=64$, centers 0 and 65 both have an empty list. At cutoff 26 their lists are empty and $\{11\}$, since $65\equiv11\pmod{27}$.

Here is the count for integer $T\ge1$. Put $M=3^{\lfloor\log_3T\rfloor}$. At the terminal cutoff, residues $1,\ldots,T$ modulo $3M$ are distinguished individually. The other $3M-T$ residues yield an empty terminal list and also give empty lists for every cutoff between $M$ and $T$. Earlier cutoffs can distinguish them only modulo $M$. Cutoff $M-1$ already distinguishes every such residue modulo $M$, using the empty list for residue zero. These remaining residues form one consecutive block cyclically, so the minimum alphabet for all cutoffs through $T$ is

$$T+\min(M,3M-T).$$

For $M=1$, the earlier query family is empty and there is just one residual class. The count concerns exact deterministic answer profiles for an already designated integral center. It gives **81** histories through 64 versus **65** terminal profiles, both fitting in seven fixed-length bits. At 81 the figures are **162** versus **82**, requiring eight versus seven bits. A Python census using direct valuations and a separate congruence rule agreed at every terminal cutoff from 1 to 100. This counting argument and finite check are independent of the earlier Lean proof for the single-cutoff bound. The published choices need not be identified with this fixed-center experiment. [Local census](check_cutoffs.py) · [Earlier observation model](../slot3-witness-memory/README.md)

For a future learned reader, provide the bound record and the query while withholding the center. Score supported positives, unsupported answers, coverage, and identification of a substituted witness against the exact oracle. The Nous observation-fiber theorem supplies the criterion for what the record determines. Shao and colleagues' *DeepSeekMath-V2*, pp. 3–5, separately assess a proof's score and the quality of the explanation supporting it. That distinction motivates grading the reader's witness justification separately from its answer. No model behavior was measured here. **Local study** (local archive path: `../../nous_provenance_study/papers/part_I.tex`) · **Shao et al.** (local source; not included in this repository)

## Reproduce

Run from this folder with the neighboring checkout and the toolchain used by the earlier experiment.

```sh
python3 -B check_cutoffs.py
python3 -B check_density.py
python3 -B replay.py --toolchain "$LEAN_DIR" --mathlib "$MATHLIB"
```

The replay driver authenticates the pinned compiler and Mathlib environment using the earlier project's verifier and separately kernel-replays the local Lean modules. [Replay record](verification.json). These are bounded controls and a base-field proof. The full RH entry point and a learned memory implementation are outside this assessment.
