# Kernel replay of the dropped-prime budget

The Lean module imports the original discriminant loss module and proves four declarations under its window, order and signal hypotheses. The shared nonnegative order constant precedes all prime-set and scale choices. The combined theorem bounds the normalized sum of logarithms over any prime subset covered by the two source classes. Classification of the chosen host's dropped support is documented in the [family trace](../DROP_TRACE.md).

The recorded run authenticated the pinned sources for all 36 original modules and reused the matching 36 compiled objects from the [previous published replay](https://github.com/nousentllc/riemann-hypothesis/blob/1f15c9441034d5d74949d25a498937653f6779a7/research/uriel/experiments/orbit-loss-trace/evidence/discriminant/verification.json). It compiled the new supplement and ran the separate kernel checker on both the original discriminant module and the supplement. All four declarations report `propext`, `Classical.choice`, and `Quot.sound`. The full RH entry point and Mathlib were outside this replay. [Machine-readable receipt](verification.json)

Prepare the pinned original sources, helper checkout, Lean and Mathlib using the [original reproduction notes](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). For a fresh rebuild run from this directory

```sh
python3 -B replay.py --checkout "$CHECKOUT" --original "$ORIGINAL" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB" > verification-local.json
```

For the cached mode used here, also pass `--cache "$ORIGINAL_OBJECTS" --prior-receipt "$PRIOR_RECEIPT"`. The cache must have the object contents recorded in the preceding discriminant study. Different platform builds can use the fresh mode. The script checks every source file against the original Git tree and verifies the compiler and package revisions.
