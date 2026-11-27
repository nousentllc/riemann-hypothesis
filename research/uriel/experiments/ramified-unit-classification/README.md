# Ramified Gram-fiber mass classes

The original rank-one Gram-fiber mass on the rank-three Gaussian lattice takes exactly two values at every valuation `4k` with `k ≥ 1`. The classifier is the coefficient of `π` in the residual unit, reduced modulo two. Here `π² = 2`, the field is the dyadic completion of `ℚ(√2)`, and scalar Haar measure gives the valuation ring mass one.

| Scalar `s = 4^k(a+bπ)`, with `a` odd | Original lattice mass |
| --- | --- |
| `b ≡ 0 (mod 2)` | `2 + 2/256^k` |
| `b ≡ 1 (mod 2)` | `2 − 2/256^k` |

Both values occur for each admissible disintegration. The first permanent tube-ratio cutoff is `4k+2` for every unit. One digit earlier every target on the shell occupies the same ball, with ratio two. The positive class contains the nonsquare unit `1+2π`. At `k=1` it gives `257/128`, the value of the square target.

## Read and verify

- [Single LuaLaTeX source](Ramified_Gram_Fiber_Mass_Classes.tex) · [PDF](Ramified_Gram_Fiber_Mass_Classes.pdf) · [ZIP](Nous_Ramified_Gram_Fiber_Mass_Classes.zip)
- [Replay receipt](verification/receipt.json) · [Paper verification](verification/paper.json) · [Study protocol](PROTOCOL.md)
- [Independent all-address experiment](dilates/unit_experiment.py) · [Exact results](dilates/unit_results.json)

| Proof obligation | Lean declaration |
| --- | --- |
| Every integral unit reduces to one of the two displayed representatives | [`RamDilate.UnitClass.decomposition`](dilates/UnitResidue.lean) |
| Twenty-four coarse positive target counts | [`low2_one`, `low3_one`, `low3_two`](dilates/UnitLow.lean) |
| Every perturbed positive count equals the square count | [`RamDilate.UnitClass.same_as_square`](dilates/UnitCounts.lean) |
| Both masses at all later even and odd depths | [`RamDilate.UnitClass.all_late`](dilates/UnitCells.lean) |
| Sharp cutoff for each unit | [`RamDilate.UnitClass.sharp_stabilization`](dilates/UnitDepth.lean) |
| Exactly the two masses on the original valuation shell | [`UnitTransport.exact_range_at_exponent`](dilates/UnitEndpoint.lean) |
| Both distinct masses across all scales in one family | [`UnitTransport.values_distinct`, `UnitTransport.realized`](dilates/UnitEndpoint.lean) |

The primitive count is constant under shifts by multiples of eight. Descending in the all-divisible subtype preserves the target class and contracts density by (1/16). The positive-class counts at residual exponents zero and one supply the new anchors. Once the proof reaches exponent two, two targets in the same positive class differ by a multiple of eight. The inherited companion-cylinder proof supplies the other sign. At the first scale, half of the gap between the two masses comes from losing the all-two-divisible stratum. The other half comes from the smaller primitive count after exactly one common division by the uniformizer.

Run `python3 verify.py` to regenerate the finite controls and validate the study and paper receipts. The six new modules were elaborated and checked by the standalone kernel against the inherited 114-module clean replay. The replay command verifies the complete study manifest and hashes for 1,038 pinned original source files and their respective original compiled objects.

```sh
python3 verification/replay.py \
  --sdk /path/to/lean-4.33.1 \
  --mathlib /path/to/pinned/mathlib \
  --objects /path/to/pinned/original/olean-tree \
  --original /path/to/pinned/original/repository/src \
  --work /path/to/empty/replay-directory \
  --receipt /path/to/replay-receipt.json --jobs 3
```

Use the [cache-restoration instructions in the square-dilate edition](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) to obtain the matching original objects and Mathlib. The [third edition](https://github.com/nousentllc/riemann-hypothesis/tree/1747b933087347e26863fbcb3dbb82debd0441e0/research/uriel/experiments/ramified-companion-lean) preserves the clean companion replay. The scope of the study is the stated local Gram datum and shell family.
