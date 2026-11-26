# Can one recover the same arithmetic witness?

## Expanded second edition

**Follow-through.** The [selected-place study](../selected-place-transport/) checks the stronger original Host record on the compatible branch. The prime 11 passes the five prime conditions and fails the full host rank condition. Every full host retaining d=9239 has at most 44 signed indices, which rules out an injection on the actual selected readable set.

[Paper](Recovering_the_Arithmetic_Witness_Expanded.pdf) · [Single editable LuaLaTeX source](Recovering_the_Arithmetic_Witness_Expanded.tex) · [Complete ZIP](Nous_Fixed_Datum_Host_Expanded.zip) · [First edition](../fixed-datum-host/) · [Earlier architecture paper](../window-remainder-architecture/)

The readable parameters support the original five prime conditions for some auxiliary prime **exactly when 32 does not divide the readable modulus**. In every passing case, 11 works. This classification replaces the first edition’s one-sided obstruction and single compatible example. Choosing 11 also prevents the readable modulus from dividing the old conductor component QS. The theorem stops before the construction of the old host.

The old sign kernel is explicitly in bijection with the product of the two signs and the old index group. A supplied rational isomorphism of host fields yields a bare finite bijection from readable places onto that signed carrier. An arithmetic map preserving the selected set, its character data and the old coset shares has yet to be constructed. [New Lean declarations](RecoveryCriteria.lean)

The paper derives the exact integer feasibility test for abstract coset quotas and the discrepancy between multiplicity-weighted and unweighted shares under a two-sheet projection. Seven signed objects can have exact weighted shares 4/7 and 3/7, yet their five unsigned images have shares 2/5 and 3/5. The resulting error is 6/35. The derivations are on paper with independent rational-arithmetic controls. The examples do not enumerate the actual admissible datum. [Control program](diagnostics.py) · [Exact results](diagnostics.json)

The expanded controls tested 381 admissible prime records, 136,188 nonempty subsets across four cyclic groups, 574 quota-feasibility comparisons, and 44 two-sheet multiplicity patterns. Six experiment modules were compiled and kernel-replayed for this edition against the two pinned environments. The scalar dictionary and the unsuccessful transitive port are cited from their earlier runs. [Replay receipt](replay_receipt.json)

## Reproducing the checks

The original pin is [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005). The readable pin is [e063a923](https://github.com/leanprover-community/riemann-hypothesis/tree/e063a923620ee7787b4a1270421478645bf66bdb). See the [source map](source_map.json) for file hashes and declaration locations. The original frame and host text in [WitnessInterface.lean](WitnessInterface.lean) comes from the cited original authors. The [extractor](interface.py) takes literal sections of three original files. It changes the import header and supplies namespace and section delimiters.

Use prepared native project builds for the two pins with their pinned Mathlib dependencies. The original entry module needed is `Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales`. The readable entry module is `New.Reduction.OneSidedBound`. The working run used local compiled imports. Full builds and their large caches are outside this archive. The relative locations below assume the source trees and Lean installations are siblings of the extracted folder. The original project library path can also point to a separate directory of pinned compiled modules.

```sh
python3 -B controls.py > rerun.json
cmp rerun.json controls.json
python3 -B diagnostics.py > expanded-rerun.json
cmp expanded-rerun.json diagnostics.json
python3 -B replay.py original --original ../original --sdk ../lean-4.33.1 \
  --old-objects ../original/.lake/build/lib/lean --old-mathlib ../original/.lake/packages/mathlib \
  --receipt original-run.json
python3 -B replay.py joint --original ../original --readable ../readable \
  --sdk ../lean-4.35.0 --receipt joint-run.json
```

The joint mode compiles and independently kernel-replays the old interface, the native readable experiment, its scale control, the cross-edition comparisons, and the expanded prime and signed-carrier theorems. The original mode does the same for the same-set consumer in its own toolchain. The two runs verify hashes of the pinned source files, the Lean compiler revision and Mathlib commit. The runner stops on a failed compiler, failed checker or printed placeholder axiom. The [release receipt](replay_receipt.json) records source and object hashes, printed axiom lists and checker output. Object hashes identify this build and may vary across machines. No full RH rebuild was performed.

In the first edition, trying to import the full old transitive dependency chain directly into Lean 4.35.0 fails at line 74 of the old quotient-group proof. The old consumer succeeds in Lean 4.33.1. The cross-edition result uses the literal interface in 4.35.0. The [receipt](replay_receipt.json) also preserves the unsuccessful elaborator diagnostic. The exact classification of the prime conditions is a proved mathematical obstruction independent of that diagnostic.

The [finite controls](controls.json) enumerate residue fibers and all 11,440 seven-element subsets of a 16-element cyclic group. The residue controls use illustrative tower indices and the cyclic test isolates the share predicate. Neither enumerates the fixed datum. The source and paper identify where arithmetic computation ends and existence is used.

## Building the paper

Run LuaLaTeX three times on `Recovering_the_Arithmetic_Witness_Expanded.tex` with Latin Modern and the packages in the preamble. The single source contains the original Nous PNG. For a timestamp-stable build use `SOURCE_DATE_EPOCH=1795694400` and `FORCE_SOURCE_DATE=1`. The release test rebuilt the PDF from the extracted ZIP on the same TeX installation and compared bytes. To verify the archive contents, run `shasum -a 256 -c SHA256SUMS` in the extracted folder.
