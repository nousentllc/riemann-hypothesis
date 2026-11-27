# Ramified companion Gram fibers

Let `v` be the dyadic place of `F = ℚ(√2)`, and use the rank-one Gaussian Gram construction over `F(i)/F` with the rank-three identity form. Write `πᵥ` for the uniformizer transported from the model `ℚ₂(√2)`. For each `k ≥ 1` and each integral unit `u`, the specified original lattice has regular-fiber mass **`2 − 2/256^k`** at scalar `4^k(1+πᵥ)u²`. The disintegration is arbitrary subject to the pinned hypotheses, and its scalar Haar measure gives the valuation ring mass one.

The sharp cutoff for the normalized congruence-tube ratio is `4k+2` uniformizer digits. At `4k+1`, the companion and square target balls coincide and both ratios equal two. At scales `k=1,2`, the companion masses are `255/128` and `65535/32768`. The square masses are `257/128` and `65537/32768`.

| Proof step | Lean declaration |
| --- | --- |
| A sum of squares cannot have odd imaginary coefficient modulo two | [`RamDilate.Companion.no_companion_unit`](dilates/CompanionObstruction.lean) |
| The four residual target bins modulo eight have identical counts | [`RamDilate.Companion.low3_twice`](dilates/CompanionLow.lean) |
| Primitive counts lift uniformly after reduction modulo eight | [`RamDilate.CompanionPrimitive.primitive_later`](dilates/CompanionPrimitive.lean) |
| One normalized count on the entire resolved target cylinder | [`RamDilate.Companion.band`](dilates/CompanionCounts.lean) |
| Exact ratio at all late depths, with a mismatching predecessor | [`RamDilate.Companion.sharp_stabilization`](dilates/CompanionCells.lean) |
| Named-place mass on `latV gb v`, with an admissible family serving all scales and units | [`CompanionTransport.original`, `CompanionTransport.realized`](dilates/CompanionEndpoint.lean) |

The all-`π`-divisible count is (64) times the count after division, while the denominator grows by (1024). The ratio therefore contracts by (1/16) per descent. At target (4(1+π)), the primitive part is (15/8). Vectors of exact minimum valuation one give (15/128). Vectors divisible coordinatewise by two would descend to a sum of squares with odd imaginary coefficient modulo two, so that stratum is empty. Their absence accounts for the deficit. The finite proof extends to all targets in the resolved coefficient cylinder, which places both coefficient children of any late odd-depth ball inside the same constant-density region.

## Read and reproduce

- [Single LuaLaTeX source](Ramified_Companion_Fibers_Verified.tex) · [PDF](Ramified_Companion_Fibers_Verified.pdf) · [ZIP](Nous_Ramified_Companion_Fibers_Package.zip)
- [Replay receipt](verification/receipt.json) · [Build and PDF checks](verification/paper.json) · [Study protocol](PROTOCOL.md)
- [Independent integer convolution](dilates/companion_counts.py) · [Exact results](dilates/companion_counts.json)

Run `python3 verify.py` to reproduce the independent finite controls and validate source hashes against the receipts. To reproduce the formal checks with the pinned tools and dependency cache, run

```sh
python3 verification/replay.py \
  --sdk /path/to/lean-4.33.1 \
  --mathlib /path/to/pinned/mathlib \
  --objects /path/to/pinned/original/olean-tree \
  --original /path/to/pinned/original/repository/src \
  --work /path/to/empty/replay-directory \
  --receipt /path/to/replay-receipt.json --jobs 3
```

Use [the inherited cache-restoration instructions](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) to obtain the matching original objects and Mathlib. The replay covers 114 local study modules against the compiled dependency base and verifies the identities of 1,038 pinned original dependency objects and their source blobs. The original RH archive and Mathlib were used as pinned dependencies. The corresponding complete clean builds fall outside this replay.

Earlier editions remain available in the [square-dilate study](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) and the [written companion checkpoint](https://github.com/nousentllc/riemann-hypothesis/tree/1da9522e3ada6c5af62c014ea76e77cc40ff3676/research/uriel/portfolio/ramified-companion).
