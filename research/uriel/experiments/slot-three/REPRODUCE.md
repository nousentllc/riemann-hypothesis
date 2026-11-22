# Reproduce the conductor-one experiment

Use a Git checkout of this experiment branch with the published source commit available locally. Run the following from the repository root. The two numerical programs require only standard-library Python. Use Python 3.11 or newer for the source and build drivers. In the recorded run the finite tables were reproduced under Python 3.9.6 and 3.13.2.

```sh
ROOT=$(git rev-parse --show-toplevel)
PIN=40e56bab026552e089d7afcfeff08d2defb9c005
EXP="$ROOT/research/uriel/experiments/slot-three"
T=$(mktemp -d)
mkdir "$T/original" "$T/evidence"
git archive "$PIN" | tar -x -C "$T/original"
cd "$EXP"
python3 -B field_checks.py > "$T/field.json"
cmp "$T/field.json" results/field_checks.json
python3 -B membership.py > "$T/weights.json"
cmp "$T/weights.json" results/weights.json
python3 -B source_spans.py --source "$T/original" --out "$T/spans.json"
cmp "$T/spans.json" results/source_spans.json
```

The first program checks the two finite cyclotomic fields and a quadratic class-number control at discriminant −23. The second evaluates all 5,184 weight-residue combinations and compares the strict cutoff with the weak one. The third rehashes each cited source interval and checks the full containing file against its Git blob. [Finite field results](results/field_checks.json) · [Residue enumeration](results/weights.json) · [Source spans](results/source_spans.json)

## Rebuild and replay the targeted Lean modules

Install the pinned Lean toolchain and the pinned Mathlib cache. The drivers check the Lean commit and package revisions. Supply absolute paths to their checkouts. The original sources stay separate from writable compilation directories.

```sh
elan toolchain install leanprover/lean4:v4.33.1
LEAN_DIR=$(elan run leanprover/lean4:v4.33.1 lean --print-prefix)
git clone --depth 1 --branch v4.33.1 https://github.com/leanprover-community/mathlib4.git "$T/mathlib"
(cd "$T/mathlib" && PATH="$LEAN_DIR/bin:$PATH" "$LEAN_DIR/bin/lake" exe cache get Mathlib)
set -- --source "$T/original" --toolchain "$LEAN_DIR" --mathlib "$T/mathlib"
python3 -B build_tower.py "$@" --workers 5 --work "$T/tower" --out "$T/evidence"
python3 -B check_slot.py "$@" --tower "$T/tower" --work "$T/local" --out "$T/evidence"
```

The first stage provides 1,101 original project modules and individually replays eight original endpoints. Each original source must match the pinned Git blob. The second stage authenticates all 1,100 original modules in its import closure, compiles all nine experiment modules and replays each with `leanchecker`. All 19 audited declarations list exactly `propext`, `Quot.sound` and `Classical.choice` as their transitive axioms. The stage checks that two attempted substitutions fail with type mismatches. One substitutes the bottom-field class-number proof for the all-layer hypothesis. The other substitutes a generic bound for evidence that 1 belongs to the chosen set. [Original module manifest](results/tower_build.json) · [Local kernel replays and rejected controls](results/joint_check.json) · [Direct proof dependencies and transitive axioms](results/proof_terms.json)

Of the 1,101 original modules in the recorded build, 451 were compiled for this experiment and 650 came from authenticated earlier builds. The recorded run used seven workers and the optional `--cache "$PREVIOUS_BRIDGES"` argument. That directory held the earlier joint-witness build's `lib` directory. The driver authenticates every reused compiled object against the prior manifests. In the first attempt the compiler's default typeclass-search allowance was too small for an original local-fields interface. The restart read the field-library option `synthInstance.maxHeartbeats=400000` from the pinned Lake configuration. It compiled the corresponding field modules with that setting and reused only compatible checkpoints. An empty scratch directory and the command above reproduce the same theorem checks without the previous build. Object hashes and diagnostics can vary by platform.

## Focused checks

```sh
python3 -B base_field.py "$@" --work "$T/bottom" --out "$T/evidence/base_field.json"
python3 -B check_formal.py "$@" --work "$T/formal" --out "$T/evidence/formal.json"
```

To compare the original and prescribed versions of Part B, supply the original module library and manifest produced by the tower stage. This procedure also checks that the exact published statement follows by forgetting the prescribed set. The optional earlier bridge-cache procedure is described in the focused report. [Part B comparison](PART_B.md)

```sh
python3 -B prescribed_part_b.py "$@" --cache "$T/tower/lib" --manifest "$T/evidence/tower_build.json" --work "$T/prescribed" --out "$T/evidence/prescribed_part_b.json"
```

## Verification limits

Lean checks the bottom-field class number and cyclotomic level unconditionally. The field-specific tower and exception theorems take an explicit assumption about the class group of every layer from index 2 onward. The class groups of the source's field and the standard cyclotomic field at every positive layer have the same cardinality, by a locally checked isomorphism of number fields, integer rings and ideal class groups. The external input is exactly Yokoi's regular-prime nondivisibility theorem in the standard fields. Our kernel run does not formalize that theorem or compute the proof's selected center. The finite certificates resolve exactly two class numbers. The named original modules and the new implications use the official Lean kernel with cached Mathlib. A full rebuild of `Main`, replay of every dependency in an empty environment and independent-kernel verification were outside this run. [Arithmetic and external theorem](ARITHMETIC.md) · [Actual selection and information it retains](CENTERS.md)
