# Reproduce the retained-host experiment

## Start with the finite control

Run the following from this experiment directory with Python 3.11 or later. The enumeration uses only the standard library and exact rational arithmetic.

```sh
python3 -B share_counts.py > /tmp/uriel-share-counts-replay.json
cmp share_counts.json /tmp/uriel-share-counts-replay.json
```

The computation covers all seven-element subsets of the eight-element group and all 40,320 permutations. The JSON gives the eight omitted residues, their exact thresholds, the parity character sums and the permutation totals.

## Lean environment

Use a checkout of this experiment branch containing both the original proof commit `40e56bab026552e089d7afcfeff08d2defb9c005` and the prior experiment commit `e674cb750ef96b2f5e7cd46586ea4edb9998715a`. The verifier reads the older wrapper sources and the two original build manifests directly from the latter Git object. Use Lean 4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and a prepared Mathlib checkout at `0df444a360eaa60ab8c11dca51a86af692955474`. The package checkouts and their compiled libraries must match the pinned lake manifest. The prior experiment includes the setup directions. [Toolchain and Mathlib setup](../joint-witness/REPRODUCE.md)

Set `LEAN_ROOT` to the toolchain directory containing `bin/lean`, `bin/lake` and `bin/leanchecker`, and `MATHLIB_DIR` to the prepared Mathlib checkout. From this experiment directory the following commands extract the source into a temporary directory with enough disk space and run the complete experiment. The scratch library should be empty at startup.

```sh
REPO=$(git rev-parse --show-toplevel)
TRIAL=$(mktemp -d)
mkdir "$TRIAL/original"
git -C "$REPO" archive 40e56bab026552e089d7afcfeff08d2defb9c005 src |
  tar -x -C "$TRIAL/original"
python3 -B verify.py \
  --source "$TRIAL/original" --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB_DIR" \
  --work "$TRIAL/build" --out "$TRIAL/verification.json" --workers 3
```

Without a project cache this rebuilds the entire targeted original dependency closure. To use an existing compatible build of the original project, append one or more `--cache-lib /path/to/lib` arguments. Supply a directory containing the package trees such as `Development` and `Formalism`. The previous joint experiment's final unified library worked for this run. The optional cache can omit modules. Every reused original must match both the pinned Git blob for its source and the recorded SHA-256 for its compiled object on the matching platform and toolchain. A mismatched object stops verification. On a different platform the verifier takes the source-rebuild path. Every new, generated, and imported prior-experiment module is compiled afresh.

## What the verification covers

1. Check Lean's Git revision and the tracked revisions and cleanliness of Mathlib and its manifest packages. Validate the bytes of every original source in the targeted import closure against its pinned Git blob. Materialize that closure, and only authenticated original objects or fresh compilations, in the scratch library.
2. Reconstruct the inverse-scale variants from the pinned source. Every specified replacement must have exactly one match. Source hashes of the generated variants and local wrappers are recorded. Verify the prior joint-witness wrappers' source hashes against their committed manifest and compile them afresh.
3. Compile every handwritten and generated experiment module in import order with the recorded flags. Run `leanchecker -v` for each such module and each prior wrapper in the new closure. The checker replays the named target module against its import environment. Source and object authentication for imports has a different scope from kernel replay of all imported modules.
4. Inspect direct proof-body references required by `Audit.lean`. Missing edges fail inside Lean. Audit the fully qualified axiom names of theorem declarations in the freshly compiled experiment, generated and earlier wrapper modules and check they belong to the standard whitelist. Check the finite Python result byte for byte.
5. Save the JSON report only after every check succeeds. The module digests, source graph, direct original import roots, exact toolchain, aggregate digest of the original source/object inventory, new original compilations, replay transcripts, audited edges, and axiom inventories identify the extent of this run.

Compare finite outputs byte for byte. For the formal replay compare hypotheses, theorem declarations, axiom sets, edge rows and replay transcripts. Rebuilt object digests and the split between reused and freshly built original modules can depend on platform and build environment. The experiment verifies a selected dependency closure. The full formalization and the declarations supplying any explicit premises outside the tested closure have a wider scope. [Recorded verification](results/verification.json)
