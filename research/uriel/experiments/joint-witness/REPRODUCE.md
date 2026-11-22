# Reproduction and verification scope

The [fixed-pair replay](results/fixed_pair.json) and the finite outputs are available. The original bridge and same-index modules are undergoing scoped compilation and replay.

Run these commands from the repository root. The finite experiments use standard-library Python. The original-module runs also use the official Lean v4.33.1 toolchain, the pinned Mathlib checkout and its binary cache. The package revisions are verified by the shared environment check from the second experiment. A fresh writable scratch directory keeps compiled files separate from the original source.

```sh
ROOT=$(git rev-parse --show-toplevel)
EXP="$ROOT/research/uriel/experiments/joint-witness"
TRIAL=$(mktemp -d)
PIN=40e56bab026552e089d7afcfeff08d2defb9c005
mkdir "$TRIAL/original" "$TRIAL/evidence"
curl -fL "https://codeload.github.com/leanprover-community/riemann-hypothesis/tar.gz/$PIN" -o "$TRIAL/src.tar.gz"
tar -xzf "$TRIAL/src.tar.gz" --strip-components 1 -C "$TRIAL/original"
python3 -B "$EXP/finite_probe.py" --out "$TRIAL/finite.json"
cmp "$TRIAL/finite.json" "$EXP/finite_results.json"
(cd "$EXP" && python3 -B -m unittest -v test_finite_probe)
python3 -B "$EXP/conductor_one.py" > "$TRIAL/conductor.json"
cmp "$TRIAL/conductor.json" "$EXP/conductor_one.json"
python3 -B "$EXP/center_filter.py" > "$TRIAL/centers.json"
cmp "$TRIAL/centers.json" "$EXP/results/center_filter.json"
python3 -B "$EXP/box_threshold.py" > "$TRIAL/threshold.json"
cmp "$TRIAL/threshold.json" "$EXP/results/box_threshold.json"
python3 -B "$EXP/source_trace.py" --source "$TRIAL/original" --out "$TRIAL/source_trace.json"
cmp "$TRIAL/source_trace.json" "$EXP/results/source_trace.json"
```

The archive used in this run had SHA-256 `64399e32d8dbce44d186c2f4ca5ee2a428e66b77d0c0b8a63ce0f8e5f0f8d192`. Each imported original file and every cited span is authenticated against its original commit's Git tree. A regenerated compression stream is acceptable when the source blobs agree.

```sh
elan toolchain install leanprover/lean4:v4.33.1
LEAN_DIR=$(elan run leanprover/lean4:v4.33.1 lean --print-prefix)
git clone --depth 1 --branch v4.33.1 https://github.com/leanprover-community/mathlib4.git "$TRIAL/mathlib"
(cd "$TRIAL/mathlib" && PATH="$LEAN_DIR/bin:$PATH" "$LEAN_DIR/bin/lake" exe cache get Mathlib)
```

The finite tests ran with Python 3.9.6 and 3.13.2. The Lean build driver used Python 3.13.2. The following invocation uses shell positional parameters to share the verified toolchain and source paths. Give each stage its own fresh work directory. The final local checks reauthenticate the original compiled dependencies. Worker counts can be reduced on a smaller machine.

```sh
set -- --source "$TRIAL/original" --toolchain "$LEAN_DIR" --mathlib "$TRIAL/mathlib" --out "$TRIAL/evidence"
python3 -B "$EXP/build_original.py" "$@" --work "$TRIAL/base" --workers 5
python3 -B "$EXP/build_bridges.py" "$@" --base "$TRIAL/base" --work "$TRIAL/bridges" --workers 4
python3 -B "$EXP/fixed_pair_check.py" "$@" --reuse "$TRIAL/base" --work "$TRIAL/fixed"
python3 -B "$EXP/check_joins.py" "$@" --base "$TRIAL/base" --bridges "$TRIAL/bridges" --work "$TRIAL/joins"
```

The process compiles original dependencies and individually kernel-replays named endpoints. Per-module hashes identify the local build. Source labels, compiler warnings and compiled-file digests can vary with the package setup and filename. The new declarations use the same Lean kernel and imported cached Mathlib. The local design wrapper includes four lines of authenticated class abbreviations, with their original predicates and a distinct namespace. All other source modules included in the original build stages are compiled in full. The source trace covers further upstream proofs by inspection. Whole-archive verification lies outside this experiment. [Public whole-project verification](https://math.mit.edu/~drew/grh/) · [Earlier separately replayed analytic subset](../second/VERIFICATION.md)

During the recorded run the bridge build consumed authenticated objects as the base build produced them. An initial attempt put base and bridge objects in separate directories on Lean's search path. Lean resolved a namespace against the first directory and failed to find an existing prerequisite there. We restarted the bridge build with a single assembled import directory, checking the source and object digest of each reused module. The commands above run the stages sequentially. To overlap them, start the base first and pass `--follow-base` to the bridge stage. The sequential mode rejects a missing or incomplete base record.
