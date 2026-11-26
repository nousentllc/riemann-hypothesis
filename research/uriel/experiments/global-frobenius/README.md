# Two odd Frobenius partners on original hosts

Follow-up to the [fixed-discriminant and compact spacing study](https://github.com/nousentllc/riemann-hypothesis/tree/d5cdf95bdb5634d812782c464e799f8f5d0546ee/research/uriel/experiments/frobenius-spacing). With the discriminant varying through the original host supply, two distinct odd partners occur on the same retained set at one eligible inert prime. The prime is strictly below the original cutoff and its step meets the original long-order filter.

## Evidence

- [PrimeCutoff.lean](PrimeCutoff.lean) proves the bounded same-set implication from the exact archived `HostExP P` and `GlobalTheory.Published.Linnik` propositions. It retains `RankVal`, `HostGood`, and the supplied `P`. [HostArtin.lean](HostArtin.lean) identifies the actual chosen `hPH` from the host's Artin class. Six new modules and the original least-prime interface passed local kernel replay.
- The printed manuscript gives a written proof that the original `ThinOK` and `BadOK` force one such collision onto a good orbit on the unchanged set. The normalized ramp algebra and finite weighted comparison were replayed in Lean. The full character-to-prime weight bound and its host application are written proofs.
- The separate written selector refinement produces offsets exactly 1 and 3 on a good orbit, with the original retention and bad-mass constraints. This variant can select a new mask once. The full-period same-set theorem preserves the prior mask.
- The dyadic tree gives the exact incidence count and classifies the masks without a long collision. Independent controls enumerate small masks, compare the tree recurrence against direct scans, count designated incidences and evaluate rational Bernoulli tails. These controls use synthetic cyclic groups.

The results concern original retained top partners, with separate statements for the full orbit, a good orbit and the exact offset pair. Further consumer-specific horizon, lift and gain conditions are tracked in the paper. The construction does not produce a numeric discriminant or prime. The original source and complete Riemann-hypothesis build were not rebuilt locally. [Pinned declaration trace](source_trace.json) · [Replay receipt](replay_receipt.json) · [Build scope](build_scope.json)

## Reproduce

From this directory, with Python 3:

```sh
python3 -B controls.py > results.reproduced.json
diff -u results.json results.reproduced.json
```

To replay, provide the original `src` tree at `40e56bab026552e089d7afcfeff08d2defb9c005`, Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, a prepared Mathlib checkout at `0df444a360eaa60ab8c11dca51a86af692955474` with dependencies, and an object directory containing the required original compiled modules in their module-path layout. The runner creates an isolated overlay and rebuilds the least-prime interface from pinned source. The JSON receipt records compiler, source hashes, and per-module replay output.

```sh
python3 -B replay.py --source /path/to/original/src --sdk /path/to/lean-sdk \
  --mathlib /path/to/mathlib --objects /path/to/original/objects \
  --receipt replay.reproduced.json
```

Compile the single LuaLaTeX file three times to settle contents and references. The source includes the original Nous PNG. `SHA256SUMS` covers the distributed files inside the ZIP and can be verified after extraction.

[Manuscript PDF](Two_Odd_Partners_on_Original_Hosts.pdf) · [Editable LuaLaTeX](Two_Odd_Partners_on_Original_Hosts.tex) · [Complete ZIP](Nous_Two_Odd_Frobenius_Partners.zip)
