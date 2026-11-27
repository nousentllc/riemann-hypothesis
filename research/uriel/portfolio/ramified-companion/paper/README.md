# Ramified square dilates and their companion fibers

**Second edition · 26 November 2026 · Nous Independent Research**

[PDF](Ramified_Square_Dilates_and_Companion_Fibers.pdf) · [Single LuaLaTeX source](Ramified_Square_Dilates_and_Companion_Fibers.tex) · [Reproducibility ZIP](Nous_Ramified_Companion_Fibers_Second_Edition.zip)

Section 10, on numbered pages 10–14, adds the written proof of the companion mass at the original place. At scalar `4^k(1+π)u²`, for `k ≥ 1` and an integral unit `u`, the original lattice mass is `2 − 2/256^k`. The normalized counts stabilize at uniformizer depth `4k + 2`, and the immediately preceding ratio is two. The proof first excludes all coordinates divisible by two, then pairs the next two residual bins using a nonunit coordinate.

The companion stabilization and measure transport are written proofs. The new Lean source and kernel receipt cover the modulo-two obstruction. The [first edition](https://github.com/nousentllc/riemann-hypothesis/tree/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates) supplies the full reproducibility archive for the checked square-family theorem and its inherited Lean imports. The earlier edition retains its own source, paper, and receipts.

## Reproduce the second edition

- Run `python3 -B evidence/check_counts.py | diff -u evidence/counts.json -` to check the exact finite controls.
- Build the single source three times with LuaLaTeX, using `SOURCE_DATE_EPOCH=1795669200` and `FORCE_SOURCE_DATE=1` for the recorded PDF. The original Nous PNG is embedded in the source.
- Replay `evidence/CompanionObstruction.lean` with Lean 4.33.1 and the prepared study imports from the first edition. The commands and exit statuses are in `evidence/lean-replay.txt`.

The two independent LuaLaTeX builds matched byte for byte. The PDF has 40 pages, including 36 substantive numbered body pages. Section 10 begins on physical page 13. `SHA256SUMS` covers the documents and their reproduction files inside the ZIP.
