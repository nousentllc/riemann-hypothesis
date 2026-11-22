# Reproduce the class-number ascent and witness checks

The experiment uses the original sources at `40e56bab026552e089d7afcfeff08d2defb9c005`, the previous experiment at `4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87`, Lean 4.33.1 and the package revisions recorded in the original Lake manifest. A source checkout containing both Git commits is required. Python 3.11 or newer supplies the build driver. The finite group control uses standard-library Python. The separate number-field calculations require PARI/GP 2.19.1.

## Finite controls and source excerpts

Run the following from the repository root.

```sh
ROOT=$(git rev-parse --show-toplevel)
EXP="$ROOT/research/uriel/experiments/ascent-witness"
T=$(mktemp -d)
PIN=40e56bab026552e089d7afcfeff08d2defb9c005
mkdir "$T/original" "$T/evidence"
git archive "$PIN" | tar -x -C "$T/original"
python3 -B "$EXP/ramification_control.py" > "$T/ramification.json"
cmp "$T/ramification.json" "$EXP/results/ramification_control.json"
python3 -B "$EXP/check_fields.py" --gp "$(command -v gp)" > "$T/fields.json"
cmp "$T/fields.json" "$EXP/results/certified_fields.json"
python3 -B "$EXP/check_excerpt.py" --source "$T/original" > "$T/excerpt.json"
cmp "$T/excerpt.json" "$EXP/results/transport_source.json"
```

The Python control enumerates inertia groups in the finite abelian example. The PARI run constructs the actual fields, certifies the class groups, and checks fixed classes under both order-three automorphisms. The excerpt check verifies the full originating Lean source against Git, then compares the two selected intervals and the local wrapper byte for byte. [Group computation](results/ramification_control.json) · [Certified fields](results/certified_fields.json) · [Excerpt provenance](results/transport_source.json)

## Original dependencies and local kernel replay

Install the pinned Lean and Mathlib environment following the slot-three instructions. In the commands below, `LEAN_DIR` is the absolute toolchain installation path and `MATHLIB` is the absolute path to the pinned Mathlib checkout and package cache. These checks use its compiled Mathlib library. The driver verifies the compiler's Git revision, every pinned package's Git revision and its tracked working-tree status. The original proof sources stay in an independent read-only input directory. [Toolchain and cache setup](../slot-three/REPRODUCE.md)

```sh
set -- --source "$T/original" --toolchain "$LEAN_DIR" --mathlib "$MATHLIB"
SLOT="$ROOT/research/uriel/experiments/slot-three"
python3 -B "$SLOT/build_tower.py" "$@" --work "$T/tower" --workers 5 --out "$T/evidence"
python3 -B "$SLOT/check_slot.py" "$@" --tower "$T/tower" --work "$T/slot" --out "$T/evidence"
python3 -B "$EXP/verify.py" "$@" --tower "$T/tower" --slot "$T/slot" \
  --tower-manifest "$T/evidence/tower_build.json" --slot-manifest "$T/evidence/joint_check.json" \
  --work "$T/ascent" --out "$T/evidence/verification.json"
```

On the recorded platform, the earlier slot-three tower and experiment directories were still available. The current run started in a new work directory with those two directories as inputs. When omitted, the two manifest switches default to the committed slot-three records. The explicit manifest arguments above allow fresh source builds on another platform. Use the digests produced for that environment. The audited statements and expected failures are the cross-platform checks. The file hashes identify individual build artifacts.

The driver reads local module imports, determines the original import closure and verifies each original source blob against the pinned tree. It authenticates earlier compiled objects against the supplied manifests. Earlier experiment sources are read from the exact prior Git commit. The script assembles a single project library in scratch. It compiles the missing original modules, then the complete set of local experiment modules in dependency order. Each newly built module receives its own `leanchecker -v` replay. The semilinear transport subset is independently authenticated before use. The compact original-object digest is SHA-256 of the sorted concatenation of one UTF-8 line per reused original module: its dotted module name, source Git blob and compiled SHA-256, separated by single spaces and terminated by a newline.

A checkpoint records source digests, direct rebuilt-dependency digests, the build context, compiled digests and successful replay messages. A repeat run rechecks the checkpointed objects and recompiles a changed module or dependency. Use a fresh work directory to recompile every new module. The optional `--targets` argument is reserved for development runs. The final report uses all modules in the experiment directory.

The assumption audit visits the theorem and axiom declarations in every new module through Lean's elaborated environment, including compiler-generated theorem declarations. It checks transitive axiom inventories against `propext`, `Classical.choice` and `Quot.sound`. Hashes in the report summarize each module's sorted declaration-name and axiom-list inventory. The compiler rejects unresolved theorem statements, and the driver separately rejects `sorry` declarations, incomplete explicit axiom transcripts and unexpected replay output. It also checks the working source bytes against the source used for each compilation.

Three type controls test what the finished evidence can be used for. Lean accepts the everywhere-unramified theorem with its actual base field and rejects changing that base to the rationals in a generic tower. Lean accepts the arithmetic bound on a named finite set and rejects using that bound directly as evidence that 1 belongs to the set. The last control accepts the all-layer result at the exact earlier hypothesis type and rejects supplying only the bottom-field class-number proof. Each rejection must specifically report a type mismatch. [Machine-readable verification](results/verification.json)

This run targets the arithmetic tower and its witness application. It uses the official Lean kernel with cached prerequisite objects. A full rebuild or replay of the complete RH entry point, an independent kernel implementation and identification of the published proof's selected center are outside its verification scope.
