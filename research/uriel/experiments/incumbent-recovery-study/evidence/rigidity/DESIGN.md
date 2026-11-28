# Test of support on two residues modulo eight

Fix a cyclic dyadic conductor-one group with its own numeric labels. Rank the eight residue classes by the least numeric label in each. Retain support only on the globally earliest class and the earliest class of the opposite parity. Select points independently within that support with probability 21δ/10. This is a candidate model of the exported selection rules. The earlier profile lemma assumes positive lower bounds on every inclusion probability and cannot establish this candidate.

Before execution we register the following tests.

1. Enumerate all 40,320 label orders modulo eight. Every supported orbit has the predicted proportions of allowed positions and allowed even positions. Precisely two of four odd step residues admit neither direction of an adjacent retained pair, for every labelling. Verify signs by walking actual cycles from their least label. Include the zero residue step by lifting to order 16.
2. For cell length u in {16, 32, 64, 127, 128, 129, 255, 256, 257, 512}, set δ=1/u and test every residue phase against the exact marked-cell probabilities. Record when the 1/10 lower threshold is first met on this finite grid, and whether 11/100 clears it for all u≥128 on the grid. The empty-cell event and singleton-at-an-even-position event use the same allowed residue pattern. Calculate the two probabilities as exact rational numbers.
3. Deliberately choose an occupied descendant in the odd child of its least-base parity coset. Exhibit a supported step orbit where no even singleton can occur. Check that a radius-one adjacency test counting only the even-to-odd direction can also miss reverse edges.

The finite program probes residue geometry and the cell probabilities. The source-scale bounds and the intersection with the original bad-orbit budget require a separate derivation. No mask or prime in these controls will be identified with the previously selected witness.
