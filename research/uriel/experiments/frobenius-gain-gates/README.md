# Same-set Frobenius and positive gain

This expanded edition treats the original weighted host after the bounded two-partner result in the [first edition](https://github.com/nousentllc/riemann-hypothesis/commit/cc2e70880ad9f9cb73c962d050fab6dd9fe97542). It uses the original retained set, weights and canonical Frobenius origins, with the original refill windows at every permitted lift.

For sufficiently late weighted hosts, an inert prime in the interval from $(X')^{2/3}$ to $X'/2$ has a good orbit in the original VV. A retained odd-origin anchor has its immediate successor and a second retained odd partner. The first visit has residual at least $b'/2$. At the deeper visit the minimum consumes the entire supply and residual credit is zero. The incidence and price bounds give one prime and orbit with a premium of at least $b'/4$ over the clipped fallback at every permitted lift.

## Evidence and reproduction

| Module | What Lean checks |
| --- | --- |
| [OrientedDyadic](OrientedDyadic.lean) | Sharp collision-free occupancy and the quantitative incidence bound |
| [InteriorRamp](InteriorRamp.lean) | Interior ramp and exact principal centering at the native endpoints |
| [NativeVisits](NativeVisits.lean) | Reduced exclusions, native origin parity, generator invariance and depth-three saturation |
| [NativeGates](NativeGates.lean) | Band exclusion, Cand, the original WOK rejection weight and entry into VV |
| [PremiumBudget](PremiumBudget.lean) | First residual, clipping, the finite positive-row implication and strict increase of the native gainP |

The character-weight lower bound, the same-set joint asymptotic selection and the price majorant are written proofs using the [pinned original statements](source_trace.json). The replay uses prepared original imports, with local scope recorded in the [receipt](replay_receipt.json). The study gives existential and quantitative inequalities at sufficiently late scales. It does not compute a concrete host or rebuild the whole RH archive.

Run the finite controls with Python 3 and compare their output to [results.json](results.json).

    python3 -B controls.py > results.reproduced.json
    diff -u results.json results.reproduced.json

For Lean, provide the original src tree at 40e56bab026552e089d7afcfeff08d2defb9c005, prepared original module objects, Lean 4.33.1 at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and a built Mathlib tree at 0df444a360eaa60ab8c11dca51a86af692955474 with dependencies.

    python3 -B replay.py --source /path/to/original/src --objects /path/to/original/objects \
      --sdk /path/to/lean-sdk --mathlib /path/to/mathlib --receipt replay.reproduced.json

Run LuaLaTeX three times on the single TeX file to settle the contents and references. The original Nous PNG is embedded. The ZIP includes both manuscript formats, five Lean modules, the JSON controls and receipts, and a SHA-256 manifest.

[PDF](Same_Set_Frobenius_and_Gain.pdf) · [LuaLaTeX](Same_Set_Frobenius_and_Gain.tex) · [ZIP](Nous_Same_Set_Frobenius_and_Gain.zip)
