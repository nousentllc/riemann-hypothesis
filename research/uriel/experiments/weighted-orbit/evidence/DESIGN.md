# Design and order of analysis

The previous manuscript proposed a matched comparison of the original weighted bad-orbit condition. The earlier step-two adjacency statistic is a positive control for detecting placement effects, not the target outcome. This note freezes the primary and secondary designs before the lead evaluator is executed. The definitions, the choice of parameters, and the primary example were already examined analytically, and a collaborator had reported preliminary results. This is a designed counterexample with independent replay, not a blinded or time-stamped statistical preregistration.

## Endpoints

Fix the scale, rank, cyclic frame, number-field prime data, enumeration of its elements, canonical orbit representative, prime filter, and comparison constant. Change only the retained subset. Compare the source's three conjuncts for every orbit, mark the number of retained points in failing orbits, and evaluate both sides of the source inequality. Record exact counts and threshold inequalities; log weights may also be displayed numerically.

- H1. At x=2^32, epsilon=1/64, on the cyclic frame of size 32768, use the first complete marked tile, choosing position 2 mod 4 in each even cell. At fixed anchor move the first retained point to the corresponding residue immediately beyond the tile. The bad mass should change and the Boolean inequality should cross at the chosen test constant Cb=1. Falsifiers include a second eligible prime, an additional marked tile, a short-window overload before the exchange, or a budget covering both sets.
- H2. A coordinate change that also transports the orbit generator and canonical base should preserve every local position and both outcomes. The base is part of the data. Changing only the retained set can alter the result even if the change looks like a translation in the cyclic group.
- H3. At x=2^27 and size 131072 the same single exchange should work even when both retained sets satisfy the original density interval. Outside the first marked tile retain exactly the indices with residue 0, 1, 2 or 3 modulo 7. Replace index 2 by the smallest unoccupied tail index congruent to 2 modulo 4. Inspect all complete tiles and all short windows; a surviving marked tile or a density violation would defeat this proposed strengthening.

## Interpretation

Test all consecutive circular windows, all complete (non-wrapping) tiles, the residue-index histogram, the coordinate-to-raw-label map, and the effect of threshold choice. The analytic family count, the complete one-swap neighborhood and the density strengthening are exploratory elaborations of the previously proposed fixed-histogram test. Report whether the actual distinguished subgroup is nontrivial, whether any large-window selection hypotheses hold, and which parts are an explicit computation, a source-derived existence statement or a local kernel replay. The chosen budget is a test parameter; the construction's existential budget is unknown.

## Later extension

After the index-one runs, we derived and tested a separate case with index two and exact 4:3 counts. We also checked an obstruction obtained by imposing the source rank bands, and a separate no-complete-tile arm that reaches the short-window cap. These are post-hoc mathematical constructions. Their admissibility and conclusions are evaluated by explicit witnesses, proofs and executable checks.
