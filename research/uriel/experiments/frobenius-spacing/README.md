# Frobenius partners and spacing

[Single LuaLaTeX source](Frobenius_Partners_and_Spacing.tex) · [PDF](Frobenius_Partners_and_Spacing.pdf) · [Complete ZIP](Nous_Frobenius_Partners_and_Spacing.zip)

At the previous fixed value (d=9239), the original selector has no input satisfying its literal scale-tied rank predicate. Lean proves the necessary inequality (d>94897) from the original host and `RankVal`. The proof uses the rank identity with `TOv * nWv`, so it applies at every scale.

For a general original host, the same-set Lean theorem counts the odd offsets from an actual retained anchor on a good orbit. Its bound is (K-1), where (K) is the original short-window cap. An odd displacement within a marked tile is impossible. The 16-cycle mask ({2,6,10,15}) satisfies all three literal local clauses with a complete marked tile. Anchor 15 has offsets 3 and 7 in a single short window. The matched control ({2,6,10,14}) removes every odd partner while preserving the tile and both caps. The finite fixtures demonstrate a limitation of the local conditions. Realization by a full arithmetic host remains beyond their scope.

The compact proof uses a different implication. Two retained short targets give equal mixed powers in a dyadic quotient. The selected set's three-term rule makes the first projected displacement trivial, and the native dyadic order lemma contradicts the size bound. The local result is at most one eligible exponent in the small-prime branch. The source has a separate existence test before choosing a packing.

## Evidence and reproduction

The original source pin is `40e56bab026552e089d7afcfeff08d2defb9c005`. The compact pin is `72fead102f663d5c7a407964a13dc0cf9d977207`. The source trace records Git blobs, line links and SHA-256 digests. [Source trace](source_trace.json)

- `OriginalSpacing.lean` and `OrbitControls.lean` replay under Lean 4.33.1 against prepared original imports. [Original receipt](original_replay.json)
- `SpacingLogic.lean` and `CompactOrder.lean` replay under Lean 4.35.0. The compact replay also checks the native order module built from the pinned source. The compact spacing and scale hypotheses in the joined lemma are explicit, and their use in the full datum is source-traced. [Compact receipt](compact_replay.json)
- `controls.py` independently verifies both small masks, enumerates 816 completions at order 32, checks 21 instances of the sharp occupancy family, and tests incoming conflicts. [Exact results](results.json)
- Full RH builds were outside the local replay. [Independent compact verification report](https://math.mit.edu/~drew/shortgrh/)

After extracting the ZIP, run these checks.

~~~sh
shasum -a 256 -c SHA256SUMS
python3 -B controls.py | cmp - results.json
~~~

The following commands use paths relative to the reader's own checkouts and toolchains. Supply a prepared original project object tree and a built or restored Mathlib cache. The compact runner builds the six-module native order closure when `--objects` is omitted.

~~~sh
python3 -B replay.py original --source ../original/src \
  --sdk ../lean-4.33.1 --mathlib ../old-mathlib \
  --objects ../original/.lake/build/lib/lean --receipt fresh-original.json

python3 -B replay.py compact --source ../grh-lean/grh-compact/src \
  --sdk ../lean-4.35.0 --mathlib ../new-mathlib --receipt fresh-compact.json
~~~

Compile the single TeX file three times with LuaLaTeX. It embeds the original Nous logo. The release used TeX Live 2026, `SOURCE_DATE_EPOCH=1795694400` and `FORCE_SOURCE_DATE=1`. The PDF has 34 pages, including 31 numbered manuscript pages.
