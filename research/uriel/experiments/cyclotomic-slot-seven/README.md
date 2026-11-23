# The fixed cyclotomic slot at seven

For the principal character, the fixed prime 7 contributes zero to the cohomological length sum at every permitted layer and cutoff. The same holds at 3. The exact fixed roster is {3, 7}, so the moving field at 2 supplies the only field tests still needed for the two-selection gap theorem. Its even crossover, two endpoint bounds, and the hypotheses furnishing the pair and page continue to matter. This package establishes no numerical height at which those moving tests pass.

The distinction that explains the result appears at conductor 49. Its relative class number is 43. All 43 classes in a group of that order are seventh powers. The proof propagates absence of seven-primary classes through the full tower, then applies the source's cohomological descent. It never has to find an individual exceptional center. A second, ordinary mathematical derivation gives the sharper congruence for the minus part at every height. The paper identifies the parts of this independent argument that have been checked in Lean.

## Reading the package

The single LuaLaTeX source and matching PDF are **The_Fixed_Cyclotomic_Slot_at_Seven.tex** and **The_Fixed_Cyclotomic_Slot_at_Seven.pdf**. The two vector exhibits and the original black Nous PNG are embedded in the source. The title, abstract, and contents have their own pages; the main text begins on a fresh page. The paper credits Justin Candler and includes a Human–AI collaboration disclosure describing Uriel’s contributions and the verification process. To rebuild the PDF, copy the TeX file to an empty writable directory and run LuaLaTeX twice there. The TeX distribution must contain the packages and fonts named in the preamble. The supplied PDF is ready to read.

Start with **CLAIMS.json** for the statement, evidence class, exact files and limits of each result. **PROVENANCE.json** records the original, earlier research, formal toolchain and release verification. All paths below are relative to the extracted package.

| Question | Where to look |
|---|---|
| Why do precisely 3 and 7 occur for this character? | evidence/roster/SevenRoster.lean |
| Why does the class number at the bottom equal one? | evidence/base/SevenBase.lean, evidence/base/results.json |
| Why does one ramified place suffice at each step? | evidence/ascent/SevenAscent.lean, evidence/ascent/source_map.json |
| Which original kernel, signs and field models does this cover? | evidence/descent/SevenDescent.lean, evidence/descent/SevenConclusions.lean |
| Why is conductor 2401 the right independent numerical comparison? | evidence/descent/SevenCalibration.lean, evidence/numerics/extended.json |
| What changes if the search constants were already chosen? | evidence/descent/SevenWindow.lean, evidence/ranks/SevenBudget.lean |
| What remains at 2? | evidence/moving/MovingBudget.lean, evidence/moving/source_map.json |
| Which computations succeeded or timed out? | evidence/base/pari.json, evidence/base/pari_attempts.json, evidence/numerics/pari_norms.json |
| What did the combined formal replay check? | evidence/kernel.json, evidence/input_pins.json, evidence/replay.py |

## Reproducing the evidence

From the directory containing this README, run the following for exact finite arithmetic, synthetic controls, the generated least-rank proof comparison and file integrity. Python 3.9 or newer and its standard library suffice.

```sh
python3 evidence/reproduce.py --sha256
```

With PARI/GP installed, run an independent arithmetic comparison at every tabulated conductor, including 2401. The recorded full-class certification attempts and timeouts are separate from the successful relative class-number checks.

```sh
python3 evidence/reproduce.py --pari
```

For the optional formal replay, use a checkout containing the pinned original src/ directory, a built checkout of the pinned Mathlib with its Lake dependencies, and the pinned Lean SDK containing lean and leanchecker. The optional Git checkout resolves the original and historical research objects identified in the manifest. An existing compiled-input root may be supplied repeatedly with --objects. Each reused original or prior research object must match its recorded fingerprint. With no object roots, the script builds those inputs from source. Set the shell variables below to the corresponding local paths.

```sh
python3 evidence/reproduce.py --source "$ORIGINAL_CHECKOUT" --git "$RESEARCH_GIT" \
  --mathlib "$MATHLIB_CHECKOUT" --toolchain "$LEAN_SDK" --kernel --sha256
```

To recreate the distribution ZIP from the extracted package, use the following command. The archiver checks every member, fixes the metadata and ordering, and prints the archive digest. Identical compression-library versions give byte-for-byte reproduction.

```sh
python3 evidence/repack.py --output ../The_Fixed_Cyclotomic_Slot_at_Seven_Research_Package.zip
```

The receipt distinguishes rebuilt supplements from reused dependencies. It names each audited declaration and its reported axioms. The formal replay covers this study's dependency graph. No full build of the original formalization was performed. The integer calculations and synthetic failures supply independent tests of intermediate mechanisms. Any inference about RH itself lies outside this experiment.

## Research lineage

The five initial experiment protocols were committed before testing. The carry congruence, least-rank supply, degree calibration and matched moving-budget analyses are described with their separate evidential status in the paper and records. The fixed-K endpoint theorem and the redesigned least-rank theorem answer different questions. The former preserves the user's original constants. The latter supplies a new eligible choice under the coherent-supply hypotheses. An older choice can retain both redundant odd ranks.

[Registered protocols](https://github.com/nousentllc/riemann-hypothesis/commit/23228a3b471662c68676349564a3640bd0dae5af) · [Original formalization](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) · [Prior gap experiment](https://github.com/nousentllc/riemann-hypothesis/tree/0b9ed6f42cccf214e7e196f2e129ea1e3b1b5987/research/uriel/experiments/prescribed-gap-witnesses) · [Experiment branch](https://github.com/nousentllc/riemann-hypothesis/tree/experiments/uriel-cyclotomic-slot-seven/research/uriel/experiments/cyclotomic-slot-seven)
