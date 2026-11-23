# Matched moving-layer comparison

The three theorems in `MovingBudget.lean` are conditional source-level lemmas for the prime two. The target and companion in the original `TwoBase` interface are distinct. No actual bound on the moving companion field is established here. `source_map.json` records the defining declarations and how the original proof reuses its chosen witness. `kernel.json` records elaboration and kernel replay. The enclosing experiment runner includes this module.

Run `python3 control.py` to regenerate the exact synthetic comparison controls in `results.json`. The dyadic tests use rational bounds and integer arithmetic. They test a sufficient budget inequality, not the observed two-primary lengths of number fields.
