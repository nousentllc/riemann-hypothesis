# Cofinal endpoints and the prime sum

[Read the paper](Cofinal_Endpoints_and_the_Prime_Sum.pdf) · [Edit the single LuaLaTeX source](Cofinal_Endpoints_and_the_Prime_Sum.tex) · [Inspect the evidence](evidence/)

The question is whether the arithmetic construction places endpoints close enough to recover control of a smoothed prime sum across a missing interval. The answer depends on what each endpoint certifies. Two tests on the same exceptional lists can propagate a field estimate under explicit spacing conditions. Tests at two independently constructed hosts can bound the same scalar observable when both hosts meet the original comparison hypotheses. Neither conclusion estimates the cost of an arbitrarily large unobserved interval. The paper quantifies that remaining cost for one genuine character and constructs sharp adverse examples for the information kept from the proof.

Under the original arithmetic inputs named in the paper, the selected windows can extend from Y up to Y raised to any fixed power strictly between one and two. The principal character yields an exact square window [Y, Y²]. Its character generates a group of order one, forcing the integer rescaling cap to equal one. A general character can carry a positive rescaling loss at the precise square boundary. In both conclusions the construction chooses the starting point beyond a requested minimum. The next question is whether it controls enough of the ordinarily unselected interval between different choices.

| Where to look | What you can check |
|---|---|
| [Arithmetic transport](evidence/transport/README.md) | The longer local window, the fixed scalar comparison, the marked-domain argument and the distinction between a supplied window and all locally marked scales. |
| [Fixed-character level](evidence/level/README.md) | The original TopG constructor preserves the width supplied for one character through to its level scalar, including both endpoints and every fixed positive exponent tolerance. |
| [Field and endpoint tests](evidence/collar/REPLAY.md) | Fifteen Lean declarations about field estimates, frozen witnesses, filling conditions and one common prime pair. The exact geometry controls include boundary failures. |
| [Outer-scale geometry](evidence/outer/FOLLOWUP.md) | Lean checks the coverage and closed hitting implications in the geometric model. An elementary proof and rational controls give the sharp gap factor in the logarithmic ordinate. One selection schedule attains it infinitely often. |
| [Scalar regularity](evidence/regularity/PROTOCOL.md) | A modulo-four slope bound, certified outward neighborhoods, and separate mechanized implications from a slope bound. |
| [Numerical endpoint experiment](evidence/numeric/PROTOCOL.md) | Measured heights, exact prime-power positions and guaranteed positive mass on the interval from 256 to 512. The separate [ceiling-only analysis](evidence/numeric/CEILING_ONLY.md) replaces measured heights by upper bounds. |

At normalized ceiling 0.12 both exterior ordinates pass. The true interior has positive excess mass of approximately 0.000379173 in the stated measure. Giving the certificate the values at all 33 equally spaced candidate ordinates is still a different experiment from giving it those values only when it asks for them. The reported optimum over a menu is the least number of retained readings after the menu-wide search. An oracle with access only to successive queries has a separate acquisition problem.

## Reproduce the finite results

Expand the ZIP and open a terminal in the directory containing the paper and SHA256SUMS. Use Python 3.11 or newer. This command verifies every checksum listed in the package manifest and compares six newly computed JSON outputs with their archived values. It uses the Python standard library and no network access.

    python3 -B evidence/reproduce.py

The six receipts cover the transport truth table, field-test geometry, sharp outer gaps, fixed-family slopes and scalar propagation, optimized endpoint measurements, and the ceiling-only comparison. Comparison uses full decoded JSON, including strings that represent outward-rounded interval endpoints or rational numbers. The character calculations use integer and rational arithmetic for the recorded enclosures. The runner exits with an error on a failed assertion, checksum or receipt difference. It writes its short report to standard output. Save it outside the evidence directory if desired. The checksums establish agreement with the distributed manifest. A separately trusted Git commit or archive digest establishes which distribution was received.

Four primary protocols are in the collar, transport, regularity and numeric evidence folders. The outer gap study and ceiling-only analysis are explicitly labeled follow-ups. Earlier work had already identified the modulo-four peak and approximate mass in the chosen band. This package gives a reproducible retrospective test of how much endpoint information would have certified the integral.

## Read back the pinned source

The research base is commit 08188ff0c6dd02dfec0bd65d30765862e9db56b7. The original Lean source is commit 40e56bab026552e089d7afcfeff08d2defb9c005. The runner also checks the Git blob identities of the three carried-forward numerical modules from 5396aa19afa70189268f80237c7897cdce426e24. A fresh checkout or an extracted archive of the original source is suitable for the source audit. ORIGINAL below means the directory containing src. [Research base](https://github.com/nousentllc/riemann-hypothesis/tree/08188ff0c6dd02dfec0bd65d30765862e9db56b7) · [Original source](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Earlier numerical study](https://github.com/nousentllc/riemann-hypothesis/tree/5396aa19afa70189268f80237c7897cdce426e24/research/uriel/experiments/exceptional-band-mass)

    python3 -B evidence/reproduce.py --source ORIGINAL

This also verifies the 40 files and 59 spans in the transport audit and regenerates the digest of the proposed 152-line host wrapper. Generating that particular wrapper establishes a reproducible text transformation. The separate marked-host extension develops and checks a stronger, differently structured replacement. The field trace checks 40 declaration-line prefixes in 19 files, verifies their complete Git blob hashes and checks whether each file belongs to the 701-module field import closure. The source audit authenticates all 701 field dependencies, the 408 transport import sources, two transport intermediates, 754 level dependencies and 1,181 host-extension dependencies. These sets overlap. If ORIGINAL has a Git checkout, the runner also compares the archived tree identities to the local Git object at the specified revision. An extracted archive is checked directly against the sealed manifests. If the source archive and the local Git object database are in different directories, add --git CHECKOUT to check both.

## Replay the Lean supplements

Set SDK to a Lean 4.33.1 distribution containing bin/lean and bin/leanchecker. Its recorded Lean commit is 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Set MATHLIB to a built Mathlib Git checkout at commit 0df444a360eaa60ab8c11dca51a86af692955474 with the matching compiled dependencies under its normal .lake directories. The machine used for the archived kernel receipts was an arm64 Mac. The package provides the experiments and manifests. The SDK, built Mathlib, its dependency libraries and the original proof sources are external inputs. [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)

    python3 -B evidence/reproduce.py --source ORIGINAL --toolchain SDK --mathlib MATHLIB

This path asks transport to build its 408 original imports from authenticated source, then compile and replay two original intermediate modules and the supplementary MarkedWindows module. The field step compiles its authenticated import closure in a fresh temporary directory and replays FieldEndpoints. Using that same build, the runner independently calls leanchecker on six original modules covering the two field estimates, their assembly, height, page-to-field transport and the prime-pair structure. The scalar and geometric steps replay ScalarCollar and GapGeometry using Mathlib. The host extension compiles source-derived declarations against the original types, and replays the results for fixed widths strictly between one and two and the exact square for the principal character. Those scalar conclusions explicitly assume TopG, ShortNorm, SmallOne and the VWinAt input for the indicated character. The separate level step authenticates its original imports and replays three declarations in LevelWindows. The archive records reuse of all 754 matching originals for this step. Source-only import builds can take considerable time and disk space. The recorded integrated checks used authenticated caches and rebuilt the missing field modules. A completely cold rebuild of all experiment dependencies was not performed for this release. A trusted set of previously built original project objects can accelerate the run.

    python3 -B evidence/reproduce.py --source ORIGINAL --toolchain SDK --mathlib MATHLIB --objects OBJECT_ROOT

OBJECT_ROOT contains module directory trees such as Development and Formalism. For the cached transport route **all 408** reference objects must match the recorded digests. Use the source-build command when that cache is unavailable. The field route authenticates available matching objects and rebuilds the remainder. Its archived run used 674 previously sealed objects and compiled 27 more. To place the field and level builds under a chosen existing directory, add --work SCRATCH. The runner creates and removes its own child directory. For the host extension, --objects can be repeated to add more object roots. The first root is the main transport, field and level cache. Additional roots apply to the extension only. It checks matches across all supplied roots and rebuilds missing originals from pinned sources. The --workers option limits simultaneous compilation in the field and level steps; its default is three.

The unified report compares the Lean release and compiler commit, Mathlib pin, supplementary source digest, declarations’ printed axiom lists and kernel replay outputs with the saved receipts. For the field build it also reconciles the count of rebuilt and reused imports. Platform strings, object digests and the division between cached and rebuilt objects may vary across machines. The replay receipts specify the mechanically checked scope. The identification of the full marked support through the final global design, the general regularity proof and the extremal continuum arguments have separate written proofs and controls. A full build of the original RH development was not run.

## Rebuild the manuscript

The editable paper carries its own illustrations and embedded evidence. Copy the one TeX file to an empty writable directory and run the following with LuaLaTeX, latexmk and standard TeX Live fonts and packages installed.

    latexmk -lualatex -interaction=nonstopmode -halt-on-error Cofinal_Endpoints_and_the_Prime_Sum.tex

The single-file build supplies the figures it needs. The expanded evidence in the ZIP is the easiest route to running the experiments.
