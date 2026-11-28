# How much of the selected arithmetic host can change?

At a scale inside one of the proof’s good windows, a prime pair, a number field, and a retained subset have to work together. We traced the selected subset into the character sum and the prime bound. A small counterexample shows exactly which information its size loses. Opening the proof of the selection theorem then gave a stronger, conditional result on a family with an explicitly strengthened requirement.

## Results

| Question | Result | Evidence |
|---|---|---|
| Can independent choices stand in for one joint witness? | Two predicates on two indices can each hold somewhere and never hold together. The proof supplies the character conditions for every index, then reads them at the index selected by the core. The index may vary with the scale. | [Host trace and Lean controls](HOST.md) |
| Does the retained size determine its coset distribution? | In the published cyclic frame on eight residues, four of the eight seven-element sets meet tolerance 1/8. At 1/7 all eight meet it. One cross-coset exchange changes the parity character sum from +1 to −1. A within-coset exchange leaves it at +1. | [Finite census and kernel-checked thresholds](SHARES.md) |
| Does that failure occur at the principal cyclic level? | There the subgroup has index one, its unique share is 100%, and every retained set satisfies the share test at nonnegative tolerance. The host still has further requirements. | [Index-one specialization](ShareControl.lean) |
| How tightly can the arithmetic host satisfy the share condition? | The selection proof establishes a relative discrepancy of 1/x before publishing the looser tolerance x^(−1+ε). A strengthened family construction carries 1/x, the arithmetic core and the original prime bound on one index. For the eligible nontrivial quotient characters the centered sum has error at most o·\|T\|/x, improving this intermediate bound by the factor x^ε. | [Source of the stronger estimate](SOURCE.md) · [Window theorem](StrongWindow.lean) · [Assembly hypotheses](Construction.lean) |
| How many replacements can the explicit-formula conditions tolerate? | On the same raw host, equal-size replacements inherit all six fields of EAtH if the new set meets the share bound. The stronger tolerance gives an explicit sufficient replacement budget. CoreAtH still calls for the new set’s own comparison data. | [Replacement theorem](ShareMargin.lean) |

The first three tests address the preregistration. The inverse-scale strengthening and its replacement budget were discovered during the trace and are exploratory deductions. The finite counterexample measures the exact strength of the predicate on an explicit frame. That frame does not meet the large-scale host construction’s size hypotheses. [Registered protocol](PROTOCOL.md) · [Finite controls registered before enumeration](SHARES_PROTOCOL.md)

## A quantitative replacement guarantee

Let $T$ be the tightly balanced set, let $U$ have the same size $m$, and count one replacement for each element in $U\setminus T$. Each coset count can increase or decrease by at most that many. This gives a sufficient condition for the original explicit-formula estimate to survive on the same raw host:
$$
|U\setminus T|\ \le\ \left(x^{-1+\varepsilon}-x^{-1}\right)m.
$$
The estimate is worst-case. A replacement within the same coset changes no share. The other five fields concern the raw host, level, scale and characters, so the whole `EAtH` record follows once the new shares do. The arithmetic core separately requires an identification of its top space with the actual retained set and bounds on weights attached to its points. There is no comparable transport of that whole record in this experiment. [Six fields of EAtH](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L145-L152) · [What the core takes](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean#L29-L42)

An exhaustive check covered 12,870 ordered pairs of equal-size subsets of the eight-element frame, across all sizes. For 516 distinct ordered pairs the maximum absolute coset-count discrepancy increased by exactly the number of replacements. The coefficient one in the general bound is attained. Run `python3 -B margin_counts.py` to reproduce this post-hoc check and the scalar substitution below. [Code](margin_counts.py) · [Results](results/margin_counts.json)

There is room for more than a single replacement at sufficiently large scales. Under the source size assumptions $N\ge x^{2+8\varepsilon}/2$ and $m\ge x^{-\varepsilon/8}N/2$, the real-valued budget on the right is at least
$$
\tfrac14 x^{1+63\varepsilon/8}(x^\varepsilon-1).
$$
For illustration, substituting $x=2^{1024}$, $\varepsilon=1/64$ gives $65535\cdot2^{1148}$. This arithmetic substitution supplies no particular host or certified cutoff at that scale. The integer guarantee is the floor of the real bound, subject also to there being that many available exchanges. [Kernel-checked size inequality](ShareMargin.lean)

## What the verification establishes

Lean 4.33.1 replayed 15 modules in the targeted experiment, including six generated modules and three earlier experimental wrappers. The axiom audit covered 98 theorem declarations including internal helpers. The union was `propext`, `Classical.choice` and `Quot.sound`. The verifier authenticated 1,205 original modules in the import closure, reused 1,202 recorded compiled objects, and compiled the other three from pinned source. It checked 19 direct references in original proof bodies.

- The pinned original calculations distinguish a universal in-family character estimate from a family index supplied by existence. We checked the actual cyclotomic supply, where the logarithmic-derivative constant is 4. The weighted selection proof, prime-pair bound, and the uses of both estimates downstream are traced to original source. [Source trace](SOURCE.md) · [Full handoff](HOST.md)
- Six generated Lean modules adapt pinned source in scratch space. The generator hashes each input to its Git object, removes the last weakening in `topsGroup`, and threads the strengthened field through the five subsequent declarations. The family theorem then requests that field before choosing an index. Its conclusion applies to a family supplied with this stronger request. It does not identify the hidden set of a previously fixed family. [Exact transformations](strengthen.py) · [Family construction](StrongWindow.lean)
- The combined theorem has four explicit premises for each primitive character ψ: the family design `TopG`, the cohomological window `VWinAt ψ 401`, and the prime-supply statements `ShortNorm` and `SmallOne`. The original library has suppliers for the last two. This experiment builds the combined implication against those premises. It does not rebuild the entire RH entry point. In particular it outputs neither a concrete cutoff, a number-field host at a named scale, nor a numerical RH test. [Combined theorem](Construction.lean) · [Original prime suppliers](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ShortNorms/Primes.lean#L5-L7)
- The independent enumeration uses rational thresholds and integer character sums. The Lean counterexample proves the threshold for all real tolerances. The replay records compiler/package pins, authenticated original modules, kernel replays, direct proof references and axiom sets. [Reproduce](REPRODUCE.md) · [Verification record](results/verification.json) · [Finite results](share_counts.json)

## Next experiment

Hold every coset count fixed, and vary the placement of points along the cyclic orbits used in `BadOK`. In an explicitly finite example, compare the weighted bad-orbit count under within-coset exchanges, with a relabeling that preserves the orbit structure as the control. First verify the literal local definition of a good orbit and the parameters for which it is non-vacuous. Then ask what change in the weighted sum a single exchange can cause. That would test a constraint the share and Fourier estimates cannot see. [Weighted bad-orbit condition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean#L35-L43)
