# Arithmetic field transport and filling of endpoint tests

The main Lean file is a supplement. Run its code with pinned original project sources and the Mathlib cache for that source revision, plus the Lean distribution indicated below. Nothing needs to be edited in the original source tree. The work directory must be a new empty directory for a clean build or a trusted previously created work directory. Source verification compares each original Lean file in its transitive project-import closure with the Git blob in imports.json. Source trace entries outside this closure are human-read references.

    python3 collars.py
    python3 replay.py --source /path/to/original-repository --mathlib /path/to/mathlib4 --toolchain /path/to/lean-4.33.1 --work /path/to/new-work --workers 4

The optional argument --objects accepts a prior project compilation directory arranged by module name. A prebuilt original is used only when its hash matches the recorded receipt. For subsequent invocations the trusted local work directory caches the objects it already verified or built. Mathlib needs its dependencies and compiled libraries in the normal Lake directories. Building Mathlib, installing Lean and building the original headline theorems are separate from this replay. Pick an arm64 macOS Lean 4.33.1 installation to reproduce the recorded platform. Object hashes may differ on another compatible installation. No network access is used by the script.

Original source is 40e56bab026552e089d7afcfeff08d2defb9c005. Mathlib is 0df444a360eaa60ab8c11dca51a86af692955474. The hot run imported 674 original project objects sealed by the previous joint-witness compilation, and compiled the remaining files in the current import closure. The prior local hashes certify reuse of that recorded local build. No equality with original release-platform opaque objects is assumed. The source checkout and project import graph are hashed, while compiled Mathlib and its dependencies are trusted build inputs. The supplemental object is elaborated first and then replayed by leanchecker. Its declarations are tested for sorryAx, and kernel.json shows the axiom list for each audited declaration. This is a targeted check of the supplemental module against its imported environment.

## What to inspect

- FieldEndpoints.lean gives the quantified hypotheses and original field predicates. The public declarations kexpRelax and finalRelax expose the exponent arithmetic. The declarations partARelax and partBRelax implement the modified number-field estimates. The declaration joint constructs finite witnesses once. The heightAt, fieldAt and fieldTransport declarations connect them to the original VAt. Window-pair integration specializes the pair to the proof's chosen scale.
- The fillActive, fillPower and fieldFill declarations delimit the power-window regime in which two successful tests extend to every intermediate ordinate.
- geometry.json is the deterministic output of collars.py, using exact rational arithmetic. It includes equality failures and interference between distinct integer labels.
- source_trace.json maps original source paths and declarations to their pinned Git blobs. PROTOCOL.md records which checks preceded the run.

In these statements all endpoint tests use the same frozen sets selected at the same outer cutoff and the same pair. The implemented character-field conclusions are conditional on the original arithmetic and height inputs. Numerical examples supply toy integers and never identify an actual exceptional center.

After the main replay, run the separate original-module checks with the same three build-path arguments.

    python3 check_imports.py --mathlib /path/to/mathlib4 --toolchain /path/to/lean-4.33.1 --work /path/to/new-work

This command stages byte copies of the target modules for kernel target discovery. When the hot-cache build uses symlinks, leanchecker can import them by name while its standalone target-discovery pass skips those links. The byte copies expose the modules to that second pass. The six direct checks concern the two field estimates, original assembly, height, page-to-field transport and the pair-good structure. The other inherited library modules are trusted imports for these replays.
