# Selected places and signed indices

## Expanded second edition

[PDF](Selected_Places_and_Signed_Indices_Expanded.pdf) · [Single editable LuaLaTeX](Selected_Places_and_Signed_Indices_Expanded.tex) · [Complete ZIP](Nous_Selected_Places_and_Signed_Indices_Expanded.zip) · [First edition](../selected-place-transport/)

This edition has **33 numbered body pages and three front-matter pages**. It reconstructs the research progression from the prime-sum identity through the weak prime test, fixed witness selection, lossless transport and the original arithmetic consumer. It explains which existence assertions survive the choice of the fixed datum and tests the consequences of changing the host fields or counting multiplicities.

### New result under the full original host hypotheses

At d=9239, the original rank condition bounds the number of indices. The frame projection then forces e≤4. The source field o⁶⁴≤2ᵉ forces o=1. Lean checks that the old cyclic subgroup is all of A, the order of A is 2ᵉ, the signed carrier has at most **32 slots**, and the literal old share predicate holds for every old retained set at nonnegative tolerance. This is conditional on a full host retaining d=9239. It does not assert realization of any listed scalar rank profile. The readable selected set remains the very same one used in the first edition. [New native Lean module](SingleCoset.lean) · [Fresh kernel receipt](single_coset_receipt.json)

The first edition's three replays certify a readable lower bound of 2¹⁰⁷¹, the coarse original capacity and the resulting transport obstruction. The second edition derives the stronger written bound |T| > 2⁵⁶⁰⁹³ from the literal scale inequalities, with exact integer checks. The finite controls also test 17 cyclic orders of the readable construction, the rank envelope with and without the coset penalty, and an example where identical one-coset shares conceal different ambient character sums. [First-edition replay receipts](replay_receipt.json) · [New exact controls](expanded_results.json) · [Pinned source trace](source_trace.json)

### Reproduction

Extract the ZIP and run the standard-library checks.

~~~sh
python3 -B verify.py
~~~

To repeat the new native proof, use the original source pin and compiled project and Mathlib libraries for Lean 4.33.1. The original and readable pins are 40e56bab026552e089d7afcfeff08d2defb9c005 and e063a923620ee7787b4a1270421478645bf66bdb. The runner checks source hashes, the compiler and Mathlib revision, and compiles the original capacity proof before the new module.

~~~sh
python3 -B replay_single_coset.py --original ../original --sdk ../lean-4.33.1 \
  --old-objects ../original/.lake/build/lib/lean --old-mathlib ../original/.lake/packages/mathlib
~~~

The readable proofs and cross-interface result can be replayed against the prepared Lean 4.35.0 project build.

~~~sh
python3 -B replay.py readable --readable ../readable --sdk ../lean-4.35.0
~~~

Run LuaLaTeX three times on the single TeX file. The original Nous PNG is embedded. For a timestamp-stable build set SOURCE_DATE_EPOCH=1795694400 and FORCE_SOURCE_DATE=1. Byte-identical output uses the same TeX installation and fonts. The release gate counted numbered body pages separately from the cover, abstract and table of contents. [Publication check](publication_check.json)
