# From the Riemann statement to the rank-one normalization

The published declaration export has **806,982 nodes** and **8,197,610 directed edges**. A breadth-first search from `riemannHypothesis` finds a **17-edge shortest route** to `CompanionTheory.PlacePermOperatorBicommutantSpan.sw_one`. Its proof body directly uses the rank-one finite-place growth theorem and the comparison error theorem. This connects the local density studies to the normalization consumer through declarations present in the original compiled proof.

The graph labels references from signatures and proof bodies separately. Its publisher folds generated declaration helpers into their source owners and omits Mathlib and Lean core nodes. The shortest route is a dependency trace under those conventions. Verifying the graph checksum, adjacency counts and route checks the export and the traversal.

[Recorded route and source locations](sw_one_route.json) · [Original graph and its conventions](https://shosonoda.github.io/lean-rh-alpoge/grh-proof.html) · [Local product growth study](https://github.com/nousentllc/riemann-hypothesis/tree/e3bf793943ea2f2eab748816b974a8a0c11bdbbe/research/uriel/experiments/parallel-growth)

## Replay

Place the published graph next to the replay script:

```sh
curl -fLO https://photos.proofsandreasons.io/alp-graph/rh/alp-declaration-graph-used-by-rh.json.gz
python3 -B trace.py
```

The replay checks the archive SHA-256 and compares the newly computed route to the recorded JSON. Expected output is `806982 8197610 17`. The original proof source is pinned at [`40e56bab`](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
