# One host through the prime bound

At a sufficiently late point of a good interval, the arithmetic construction gives us a host that meets the core estimates. The character estimate holds for **every** host index in the family at that point. We can therefore take it for the very index the core selected. Its chosen subset of the finite group appears in both proofs. This is the step that would fail if the two estimates merely promised some host each. [New Lean proof](HostHandoff.lean)

## The two inputs to the character estimate

Write `H` for the host, `φ` for its frame, and `TT` for its retained subset. The share inequality requires, for every coset representative γ, that the number of retained points in γ + A₀ differs from the prescribed share λ(γ)|TT| by at most x^(−1+ε)|TT|. This field depends on the distribution of the retained points. The bounded-character derivative field requires |L′/L(1,χ)| ≤ 4 log x for every specified primitive representative χ of each bounded host character. That field depends on the host and scale. Its type has no TT argument. The full estimate `EAtH` also includes order, kept-character, exceptional-character and pointwise bounds. [Definitions][defs] [Cyclotomic requirement][gchi]

1. **Building the subset.** In the actual cyclotomic supply, the proof first forms a prime-pair row at the scale Y. It passes that row to `topsChoiceH`, which returns a *single* finite set with the cardinality, bad-set and coset-share bounds. The proof installs that very TT into the host using a record update, and returns its share proof. The choice theorem gives existence. None of these steps outputs a list of the retained elements at a requested numerical scale. [Subset choice][choice] [Host construction][host]
2. **Proving the derivative bound.** For a bounded character and a primitive representative, `boundedTw_key` identifies a twist indexed by two binary choices, at least one nonzero. `boundedTw` invokes the derivative part of the good-pair bounds at the upper endpoint x. The host assembly constructs `EAtH` with the chosen set's share proof and the derivative bound for that host. Its constant is exactly 4. The earlier general `PreRows.eAtH` lemma yields κ.C × T.J under different premises. The actual cyclotomic assembly supplies 4 directly from the good pair. [Twist proof][twist] [Host assembly][assembly] [Character supply][supply] [General comparison][pre]
3. **Joining the arithmetic core.** The tied chain contains a distinguished index and an internally named set. The source proves equality of that set with the distinguished host's TT by elementwise membership and injectivity. It substitutes the equality before constructing `CoreAtH`. This is stronger than matching cardinalities. The previous experiment preserved a prime row and a cohomology bound at that same index. [Original equality and core][coreeq] [Previous joined witness](../joint-witness/Enriched.lean)
4. **Consuming the estimates.** Within `charsA`, the share field bounds a character sum over TT, and the derivative field bounds the primitive representative of a bounded character. `core_gm` applies this package and the core's estimates to the same host and TT. It identifies the host's statistic with the level statistic and uses the pointwise character field to bound a remainder. Thus the two displayed input fields alone are insufficient to replay this derivation. The original comparison already chooses its index in this order. The new experiment keeps the index visible at the end. [Character sum and log derivative][chars] [Statistic identity][identity] [Remainder][sig] [Prime inequality][gm] [Original window comparison][compare]

## What the new theorem says

Fix a character ψ and a window exponent λ. Under the design-existence premise and the nine original link or closure premises, `of_original_character_design` gives eD, eL and a positive tolerance limit ε₁. The order then matters.

| Choice | What is fixed or recovered |
| --- | --- |
| For each 0 < ε < ε₁ | One family F, constants K, cHH, eK, and a late threshold X |
| For every x ≥ X belonging to F.Win | An index i in F.Ix(x) and a row scale Y |
| At that i and Y | PairWin, PairRow, the cohomology bound VVle, EAtH with constant 4, the two explicit fields, and CoreAtH on host(i).TT |
| At that x | Gm(x) ≤ x^(1/2 + (eD + eL + 7)ε) at the level of ψ |
| For every requested lower bound y | A start W ≥ max(y,1,X) such that the statements hold at **every real x** in [W,W^λ] |

The final row uses this same family, constants and threshold. The index may depend on x, and the local row scale Y may differ from the interval start W. The cutoff combines the joint-witness threshold, strict lateness for the family, and the eventual comparison threshold. The latter absorbs several estimates depending on the level and constants. The published character-supply exponent is λ = 3/2. For W > 1 those intervals have positive length. The public bound is one-sided and concerns the specific weighted level statistic defined in the source. [Checked theorem](HostHandoff.lean) [Design interface](../joint-witness/OriginalDesign.lean) [Published design call][design] [Statistic][statistic] [Threshold construction][threshold]

## Stronger control at that same index

The experimental family requirement also carries the sharper share tolerance 1/x recovered inside the published subset construction. We enrich the host supply with its row before applying the universal family theorem `TopG`. The resulting family carries the sharper share at every late index. After the core chooses i, the proof specializes the sharper share to that i and its actual TT. All the earlier conclusions survive simultaneously on the arbitrarily late intervals. This is a new, stronger interface built on the pinned proofs. [Strong window proof](StrongWindow.lean) [Construction inputs](Construction.lean)

There is a quantitative consequence for character sums. Write o for the frame's subgroup index and T for its selected set. For an additive character χ trivial on A₀ in the A-factor and nontrivial on A, Lean's `tops_sum` bounds the distance of Σ(t∈T) χ(0,t) from |T|/(3o+1) by oδ|T|. Plugging the stronger tolerance into that theorem gives **o|T|/x** for the very set carrying the core. For x > 1, the earlier tolerance gives a right-hand side larger by the factor x^ε whenever o|T| is positive. This sharpens an intermediate estimate. The resulting bound on Gm(x) still has the exponent printed above. [Original character-sum inequality][topsum] [Same-index specialization](StrongWindow.lean)

## What the controls establish

For arbitrary predicates E and P on indices, we checked that every nonempty selector P contains some index also satisfying E **if and only if** E holds at every index. For necessity, take P to select one prescribed index. For sufficiency, take any witness of P. A two-element counterexample sets P(i) to “i is false” and E(i) to “i is true”. Each has a witness and their intersection is empty. Universality is exact for this formulation over *all possible* selectors. A known specific selector needs only a nonempty intersection. [Two axiom-free Lean proofs](HostHandoff.lean)

Two compiler controls require direct reuse at a different index or a different retained set to fail. Supplying the identity of the indices or sets repairs the application. The equal-set control includes an equality of cardinalities. Failure of direct substitution tests the types. A mathematical separation for the share property requires a finite example with differing coset counts, supplied separately. Neither control asserts that changing TT can change the scalar Gm(x) at a fixed level and x. [Transport controls](HostHandoff.lean) [Finite controls](ShareControl.lean)

## Verification and the remaining existence gap

The new theorem is a kernel-checked conditional consequence of the character-design interface. The direct local run compiled `HostHandoff.lean` with Lean 4.33.1 and replayed `HostHandoff` with `leanchecker`. Its main theorem reports `propext`, `Classical.choice`, and `Quot.sound`. Both selector lemmas report no axioms. This run imported the prior experiment's compiled design bridge and pinned original modules. It did not build the full original formalization or replay the derivation of all ten premises from the final endpoint. The upstream supply analysis above comes from reading the original proof bodies. All original links below pin commit `40e56bab026552e089d7afcfeff08d2defb9c005`.

The proof returns propositions of existence for the family, sufficiently late cutoff, windows, index and local row. It certifies how those objects fit together once supplied. We did not recover numerical values of those objects, evaluate a specific host character's logarithmic derivative, or test an integer against an actual cohomological exceptional set in this experiment.

[defs]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L137-L151
[gchi]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean#L42-L43
[choice]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/topsChoiceH.lean#L30-L67
[host]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean#L217-L227
[twist]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean#L45-L56
[assembly]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean#L110-L135
[supply]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean#L8-L16
[pre]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean#L129-L138
[coreeq]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean#L13-L25
[chars]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean#L105-L125
[identity]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean#L61-L74
[sig]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean#L38-L50
[gm]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L55-L74
[compare]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean#L17-L25
[design]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean#L33-L56
[statistic]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L20-L38
[threshold]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L12-L31
[topsum]: https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean#L75-L103
