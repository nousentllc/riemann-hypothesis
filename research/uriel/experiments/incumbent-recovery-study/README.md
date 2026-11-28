# What the original selection rules force

The principal conductor-one selection rules admit both negligible and positive fallback recovery on long orbits. One compatible family recovers exactly 1/128 of the global normalization, or 2/45 of its local odd-position allowance, while satisfying the original uniform selector's score and the stronger near-target cardinality. Another compatible family has negligible recovery under the same score. Which behavior the proof's particular existential witness has remains unknown. [Eight-page manuscript](What_the_Original_Selection_Rules_Force.pdf) · [Editable LuaLaTeX](What_the_Original_Selection_Rules_Force.tex)

## Evidence

| Question | Record |
|---|---|
| What does the source actually require of the already chosen witness? | [Internal score, three original window tests and exact-size construction](evidence/rigidity/AUDIT.md) |
| What does the fallback earn on a fixed orbit without either first-step edge? | [Source derivation, kernel scope and controls](evidence/branch/BRANCH.md), [five new Lean statements](evidence/branch/IncumbentRecovery.lean), [kernel receipt](evidence/branch/kernel.json) |
| Can two masks have identical counts and different directional recovery opportunities? | [Measured pair differences, Fourier test and error bound for the shared summary](evidence/SPECTRAL.md), [prespecified design](evidence/DIAGNOSTIC_DESIGN.md), [scale control](evidence/DIAGNOSTIC_SCALE.md), [recorded output](evidence/directions.json) |
| What goes wrong if one tests only the exported size bounds? | [Simpler 1/16 construction and failed strengthening](evidence/construction/CONSTRUCTION.md) |
| Which pinned source files were cited? | [Source IDs, hashes and line ranges](evidence/source_anchors.json) |

The structured and matched-count masks at group size 65,536 both have mean 16 forward pairs on the tested long orbit. Across three seeds, every structured mask had 8,192 two-way holes among 16,384 directions. The same-count controls had zero. Independent checks enumerate arbitrary label orientations, evaluate the finite sampling law exactly, and compare 128 full rational gain evaluations with the prior implementation. The full selection and prime-limit arguments are written deductions. The Lean checks cover local conditions on already supplied data. A full build to the RH endpoint was outside this experiment.

## Reproduce

Use Python 3.11 or newer. The directional Fourier cross-check additionally uses NumPy. Run the following from the study directory.

~~~sh
python3 -B evidence/directions.py --check
python3 -B evidence/construction/experiment.py --check
python3 -B evidence/construction/stronger.py --check
python3 -B evidence/rigidity/geometry.py --check
python3 -B evidence/rigidity/buffered.py --check
python3 -B evidence/branch/fixed_mask.py --check
shasum -a 256 -c SHA256SUMS
~~~

Use the [branch replay guide](evidence/branch/BRANCH.md) for the pinned Lean 4.33.1 toolchain, built Mathlib and original library requirements, including the dependency on the [previous gain experiment](https://github.com/nousentllc/riemann-hypothesis/pull/11). Its 25 local statements and four locally rebuilt source dependencies were replayed alongside the five new statements. The four rebuilt dependency objects have hashes differing from the original published inventory, as recorded in the preceding study.

To authenticate original sources, supply a checkout containing commit 40e56bab026552e089d7afcfeff08d2defb9c005 and an export of that commit containing its src/ directory. LuaLaTeX compiles the standalone manuscript.

~~~sh
python3 -B evidence/check_sources.py --repo "$RH_CHECKOUT" --original "$RH_ORIGINAL"
latexmk -lualatex -halt-on-error What_the_Original_Selection_Rules_Force.tex
~~~

[Original proof source](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Research branch base](https://github.com/nousentllc/riemann-hypothesis/tree/08188ff0c6dd02dfec0bd65d30765862e9db56b7) · [Prior prime-step estimates](https://github.com/nousentllc/riemann-hypothesis/pull/10)
