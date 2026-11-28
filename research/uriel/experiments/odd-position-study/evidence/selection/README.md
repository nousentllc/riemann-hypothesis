# Reproducing the parity selection

The [mathematical trace](SELECTION.md) follows the point at which a host receives a retained set. The two Lean supplements use original proof bodies as starting points at commit `40e56bab026552e089d7afcfeff08d2defb9c005`.

| Source file | What its Lean declarations establish |
|---|---|
| [JointParitySelection.lean](JointParitySelection.lean) | The original finite selector can carry a nonnegative extra penalty of expected size at most one quarter. Independent Bernoulli coordinates give a weighted variance bound, and a single witness satisfies the original class and bad-mass bounds together with the new weighted bound. |
| [GoodSamplingProfile.lean](GoodSamplingProfile.lean) | The literal original Good-orbit condition satisfies the needed hypothesis for any pointwise sampling rate between three quarters of the density and the full density. It gives eventual constants before the frame or profile is chosen and selects one witness with the stated three bounds. |

The first supplement derives from the original `ThickFrames/select.lean`, retaining its auxiliary first- and second-moment arguments and modifying its selection score. The second follows the bad-event argument of `ThickFrames/topsGroup.lean` and directly invokes the original `orbit_terms`, `orbit_sum` and `not_good_le` for the new profile. The new arguments live in research files. [Original finite selector](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L5-L174) · [Original host-group selection](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean#L64-L143)

With Python 3.11 or newer, run from this directory.

```sh
python3 -B finite_selection.py > /tmp/odd-position-selection.json
cmp finite.json /tmp/odd-position-selection.json
```

Use the original archive, retained-host build, manifest, Lean and Mathlib described in the [earlier reproducibility guide](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). With the variables defined there, replay both supplements from this directory.

```sh
python3 -B replay.py --checkout "$REPO" --original "$TRIAL/original" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB_DIR" --library "$TRIAL/build/lib" \
  --manifest "$TRIAL/verification.json" > /tmp/odd-position-selection-lean.json
```

The recorded run used Lean 4.33.1, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` and the independently pinned inventory of 1,205 original source/object pairs. The supplements import a transitive closure of 101 project modules. The two original reference roots together have a transitive closure of 104. This pass compiled the two supplements and kernel-replayed them and those two original roots. All four new named theorems report only `propext`, `Classical.choice` and `Quot.sound`. Remaining transitive imports were authenticated and reused. The grouping into canonical tree cells, prime-weight asymptotics, family lifting and extremizer calculations in the mathematical trace extend beyond the four replayed declarations. [Lean verification](verification.json) · [Exact finite results](finite.json)
