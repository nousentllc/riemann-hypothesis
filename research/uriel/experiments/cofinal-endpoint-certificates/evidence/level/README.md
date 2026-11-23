# Fixed character and arbitrary supplied host width

The original TopG takes any width λ>1 and one character-specific HostExW. LevelWindows.lean derives the HasWindows conclusion for the original cyclic-level scalar (Level.cyc ψ).Gm, at all fixed positive exponent tolerances δ. The proof does not invoke FormB, an L-function zero exclusion, or host existence for a second character. Uniform constants precede the chosen internal tolerance; the family and the cofinal windows may depend on δ and λ.

- ofTied takes a tied-family supply at a given level and width, chooses a small internal tolerance, and passes to the original scalar comparison.
- ofCharacter uses TopG, a strict width λ>1, and the original request-specific HostExW at λ to supply that tied-family input. The only assertions about marks are those implied by the unmarked HasWindows.
- twoEndpoints returns common endpoints Y and Y^λ above any prescribed lower bound, for the same ψ and δ.

Reproduce from the original revision 40e56bab026552e089d7afcfeff08d2defb9c005 with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474:

    python3 replay.py --source /path/to/original --mathlib /path/to/mathlib --toolchain /path/to/lean-4.33.1 --work /path/to/new-work --workers 4

The optional --objects path points to a prior project build. The script verifies the original Git blobs, and accepts prebuilt project modules only when their SHA-256 hashes match the registered prior build. A trusted existing --work directory can resume or reuse a build. The recorded run reuses the 754 previously sealed original modules in the closure of ZeroFreeAllOfTopG. The supplement is built and then checked separately by leanchecker against that trusted import environment. The full upstream development and Mathlib are outside this replay. See kernel.json for its receipt. The source definitions of the data-bearing statements appear in ZeroFreeAllOfTopG.lean, TopWin.lean, LevelGmLeOnFamilyScales.lean, and Window.lean.
