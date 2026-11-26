# Recovering an arithmetic witness at one integer

Every readable modulus divisible by 32 forces its quadratic prime to be 15 modulo 16. Every original raw host requires its quadratic prime to be 7 modulo 16. The main specimen realizes this incompatibility at a fixed natural number with an actual admissible datum. A second specimen at precisely the same integer passes the original prime test. For this control we rule out two direct identifications of indices. Constructing a partial transport that satisfies both original estimates remains open.

[Research paper](Recovering_the_Arithmetic_Witness.pdf) · [Editable single LuaLaTeX source](Recovering_the_Arithmetic_Witness.tex) · [Complete ZIP](Nous_Fixed_Datum_Host.zip) · [Preceding architecture paper](../window-remainder-architecture/)

## What was checked

| Question | Result | Evidence |
|---|---|---|
| Is the comparison at an integer that both data actually attain? | Yes. The least common realizable integer exists. The chosen records attain exactly that integer. Its value is noncomputable in this construction. | [Fixed datum and prime remainder](ReadableDatum.lean) |
| Can a small explicit scale realize either input? | All admissible scales exceed 2 to the power 100. The integer 400,001 is excluded. | [Scale and level-prime checks](ScaleControl.lean) |
| Can the main datum preserve its quadratic prime? | No original raw host can have the required prime 55,439. The theorem also covers any readable modulus divisible by 32. | [Joint comparison](HostComparison.lean) |
| Does the control pass the original prime clauses? | All five hold at auxiliary prime 11 and quadratic prime 9,239. Neither distinguished level prime from the readable record qualifies as the original auxiliary prime. | [Prime tests](HostComparison.lean) · [Level primes](ScaleControl.lean) |
| Can the selected readable places themselves be tracked? | Translation is injective into the readable identity fiber and the selected set is nonempty. A bijection of the entire identity fiber with the old cyclic subgroup is impossible. Under an assumed field isomorphism, all readable places number twice the old indices. | [Translation](ReadableDatum.lean) · [Two cardinality tests](HostComparison.lean) |
| Where do both original bounds act together? | On a sufficiently late eligible original scale, take the chain's stored set at its own index. Both records and the numerical conclusion are witnessed together. This theorem requires its original family and window inputs. | [Native old proof](OriginalWitness.lean) |

The fixed integer uses classical least witness and choice. Neither a decimal value of that integer nor a list of its retained places was obtained. Changing the quadratic prime falls outside the preservation test. The complete readable identity fiber, the selected subset, and the original cyclic subgroup are distinct objects. The cardinality theorem about the entire fiber leaves a partial map on the selected places undecided.

## Reproducing the checks

The original pin is [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005). The readable pin is [e063a923](https://github.com/leanprover-community/riemann-hypothesis/tree/e063a923620ee7787b4a1270421478645bf66bdb). See the [source map](source_map.json) for file hashes and declaration locations. The original frame and host text in [WitnessInterface.lean](WitnessInterface.lean) comes from the cited original authors. The [extractor](interface.py) takes literal sections of three original files. It changes the import header and supplies namespace and section delimiters.

Use prepared native project builds for the two pins with their pinned Mathlib dependencies. The original entry module needed is `Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales`. The readable entry module is `New.Reduction.OneSidedBound`. The working run used local compiled imports. Full builds and their large caches are outside this archive. The relative locations below assume the source trees and Lean installations are siblings of the extracted folder. The original project library path can also point to a separate directory of pinned compiled modules.

```sh
python3 -B controls.py > rerun.json
cmp rerun.json controls.json
python3 -B replay.py original --original ../original --sdk ../lean-4.33.1 \
  --old-objects ../original/.lake/build/lib/lean --old-mathlib ../original/.lake/packages/mathlib \
  --receipt original-run.json
python3 -B replay.py joint --original ../original --readable ../readable \
  --sdk ../lean-4.35.0 --receipt joint-run.json
```

The joint mode compiles and independently kernel-replays the old interface, the native readable experiment, its scale control, and the cross-edition theorems. The original mode does the same for the same-set consumer in its own toolchain. The two runs verify hashes of the pinned source files, the Lean compiler revision and Mathlib commit. The runner stops on a failed compiler, failed checker or printed placeholder axiom. The [release receipt](replay_receipt.json) records source and object hashes, printed axiom lists and checker output. Object hashes identify this build and may vary across machines. No full RH rebuild was performed.

Trying to import the full old transitive dependency chain directly into Lean 4.35.0 fails at line 74 of the old quotient-group proof. The old consumer succeeds in Lean 4.33.1. The cross-edition result uses the literal interface in 4.35.0. The [receipt](replay_receipt.json) also preserves the unsuccessful elaborator diagnostic. The contrast between the two prime conditions is a proved mathematical obstruction independent of that diagnostic.

The [finite controls](controls.json) enumerate residue fibers and all 11,440 seven-element subsets of a 16-element cyclic group. The residue controls use illustrative tower indices and the cyclic test isolates the share predicate. Neither enumerates the fixed datum. The source and paper identify where arithmetic computation ends and existence is used.

## Building the paper

Run LuaLaTeX three times on `Recovering_the_Arithmetic_Witness.tex` with Latin Modern and the packages in the preamble. The single source contains the original Nous PNG. For a timestamp-stable build use `SOURCE_DATE_EPOCH=1795694400` and `FORCE_SOURCE_DATE=1`. The release test rebuilt the PDF from the extracted ZIP on the same TeX installation and compared bytes. To verify the archive contents, run `shasum -a 256 -c SHA256SUMS` in the extracted folder.
