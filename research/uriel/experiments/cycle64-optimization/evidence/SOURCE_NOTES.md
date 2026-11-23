# Original-source checkpoints

The four pinned modules below connect the finite experiment to its intended selector and tile condition. The exact tree object is recorded in source_anchors.json. The experiment introduces the support word, class rates and optimization objectives. These are local definitions in this study.

| Checkpoint | Source declaration and scope |
|---|---|
| Averaging witness | The source chooses a positive-product-mass subset with a bound on the sum of squared count errors and weighted bad-orbit mass. The result exposes consequences of this choice. [select proof, lines 70–173](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173) |
| Product law | The formal caller specifies the piecewise rates, classes, bad event and count scale under which its expectation is taken. [topsGroup construction, lines 88–103](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean#L88-L103) |
| Marked cells | The source fixes empty odd cells and single even-position occupants in even cells. It also specifies the cyclic search for a marked tile and a bound on short interval counts. [Marked, CondTiles, CondIntervals, lines 9–26](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26) |
| Scales | The cell width, tile length, search multiplicity and short window arise from explicit functions of the source parameters. [Definition of goodU and associated scales, lines 237–249](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L237-L249) |

The citation checker authenticates file bytes against the original Git tree and tests line ranges on those bytes. The archive therefore records which mathematical text was read. Kernel status belongs to the declarations listed in the separate Cycle64Dual receipt.
