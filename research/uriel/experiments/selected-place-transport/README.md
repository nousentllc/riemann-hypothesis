# Selected places and signed indices

[Paper](Selected_Places_and_Signed_Indices.pdf) · [Single LuaLaTeX source](Selected_Places_and_Signed_Indices.tex) · [Complete ZIP](Nous_Selected_Places_and_Signed_Indices.zip)

For the previously fixed readable datum at q₀=18480 and d=9239, its selected set contains **at least 2¹⁰⁷¹ places**. The readable cyclotomic labelling is injective on that same set and reduces to −1 modulo q₀. Any full original host retaining d=9239 has **at most 44 signed indices and 22 unsigned retained indices**. Consequently no injective map into the original signed carrier exists at this datum. Any assignment to old cosets loses raw counts in at least one coset. Normalized shares can agree after compression, as the exact controls demonstrate.

The earlier q=11 calculation checks the five prime conditions. The full original host also imposes \(4tr+1<q\), which rules out 11. The signed capacity proof uses \(4tr+1<d\), so another auxiliary prime cannot repair the deficit with d fixed.

## Mathematical evidence

- [ReadableCapacity.lean](ReadableCapacity.lean) uses the original fixed readable term. It proves the set bound without extracting a numeral for the cutoff or a list of places.
- [OriginalCapacity.lean](OriginalCapacity.lean) uses the original native Host and Ranks types. The consumer theorem specializes the bound to the indexed original witness and its stored TT. The prime-budget theorem gives a necessary inequality depending on the size of any proposed injectively transported input.
- [SameSet.lean](SameSet.lean) checks the selected-set obstruction, the field isomorphism obstruction and the strict raw-count loss on the original quotient. It imports the prior literal frame and signed-index declarations under Lean 4.35.0. Its old frame-size hypothesis is the conclusion of the original native run.
- [Controls](control_results.json) include 2,554 old scalar rank quadruples, 485 abstract quota-size tests and three synthetic compression assignments. They exercise necessary numerical conditions and distinguish raw counts from proportions.
- [Source trace](source_trace.json) and [replay receipt](replay_receipt.json) identify the pinned files, declarations, source hashes, compiler versions, axiom queries and checker results. Replays used prepared dependency objects. The scope is the experiment modules.

## Reproduce

Extract the ZIP and run the file-integrity and exact finite checks with standard Python 3.11 or later.

~~~sh
python3 -B verify.py
~~~

The native project pins are [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and [e063a923](https://github.com/leanprover-community/riemann-hypothesis/tree/e063a923620ee7787b4a1270421478645bf66bdb). Prepare their pinned Mathlib and project build libraries. Point the commands below to your copies. The readable mode can recompile the five prior interface modules from the included sources. To reuse the exact previous binaries, add the optional --prior-objects path, which is checked against the prior receipt.

~~~sh
python3 -B replay.py original --original ../original --sdk ../lean-4.33.1 \
  --old-objects ../original/.lake/build/lib/lean --old-mathlib ../original/.lake/packages/mathlib
python3 -B replay.py readable --readable ../readable --sdk ../lean-4.35.0
~~~

Run LuaLaTeX three times on the single TeX file. The original Nous PNG is embedded. For a reproducible timestamp use SOURCE_DATE_EPOCH=1795694400 and FORCE_SOURCE_DATE=1. Byte-identical output requires the same TeX Live installation and fonts.
