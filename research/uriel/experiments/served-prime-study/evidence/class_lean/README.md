# From the family’s zero-free boxes to an unsmoothed character estimate

The first supplement imports the original `MainIn` and `PsiThin`. Its five checked statements make explicit which parts of the moving-field argument follow directly from those imports.

| Declaration | Mathematical content |
|---|---|
| `noExc_of_goodFor` | A zero-free rectangle of nonnegative height rules out a real exceptional zero within the specified width. |
| `noExc_of_boxes` | This holds for each primitive representative of the three signed host functions because all three have their own box for the same host. |
| `family_psi_estimate` | There are constants preceding the choice of family, scale and host. For each covered primitive representative, the original unsmoothed centered von Mangoldt estimate then holds at every admissible argument. |
| `conductor_envelope` | If \(t\ge1\) and \(1\le\lambda\le t^{2/3}\), its normalized error is at most \(4At^2\exp[-(c/2)t^{1/3}]\). |
| `envelope_tends_to_zero` | That upper bound tends to zero with \(t\), for fixed positive \(c\). |

A second, independently checked module proves `three_representatives` for every original host. It constructs primitive nonprincipal characters of levels exactly \(q,d,qd\), verifies all three induction hypotheses for the signed functions, and identifies their values on every natural number. For the first two characters the formula is the Jacobi symbol with denominator the corresponding prime. For the product the formula is the pointwise product. The evaluation therefore covers prime powers and the zeros at primes dividing the individual conductors.

The original admissibility condition is \(\log N\le\lambda\) for the primitive conductor \(N\). The family theorem assumes that the primitive character induces the indicated signed function on units. The [arithmetic trace](../CLASS_TRACE.md) gives the mathematical arguments for fitting the conductors beneath the envelope, converting von Mangoldt sums to prime sums, and obtaining the limiting class weight. Those steps and the final served-prime asymptotic have a wider scope than the six declarations checked in this directory.

## Reproduction

Prepare the two pinned Git commits, original source archive and retained-host build as in the [retained-host reproduction guide](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). In the following command, `REPO` names the experiment checkout, `TRIAL` the retained-host scratch directory from that guide, `LEAN_ROOT` the Lean environment and `MATHLIB_DIR` the built Mathlib checkout. Run from this directory.

```sh
python3 -B replay.py --checkout "$REPO" --original "$TRIAL/original" \
  --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB_DIR" --library "$TRIAL/build/lib" \
  --manifest "$TRIAL/verification.json" > /tmp/served-class-verification.json
```

Adding `--representatives` to the same command runs the independent second supplement. Redirect its output to a separate file to preserve both records.

The recorded verification used official Lean 4.33.1 on Apple ARM and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. For the retained-host build’s recorded platform, the verifier also checks the aggregate source/object digest against the separate manifest committed at `9ac7e1b`. For a different platform it uses the independently prepared retained-host build record there. Lean object hashes can depend on the platform.

The verifier authenticated 1,205 original source/object pairs. The two imported roots have 419 original project modules in their joint transitive closure. The verifier freshly compiled the supplement and ran `leanchecker -v` on both original roots and the supplement. All five reported axiom inventories contain `propext`, `Classical.choice` and `Quot.sound`. The other imported modules remained cached in this pass. [Recorded output](verification.json)

The separate representative replay compiles `ClassRepresentatives.lean` from its original imports and replays it with its three direct original roots. Its single theorem reports the same three axioms. [Representative verification](representatives_verification.json)
