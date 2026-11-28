# Carrying an explicit set through the odd-prime estimate

The published odd-prime argument takes an arithmetic bound, calls `Win.exc`, and obtains an existential family of finite sets. After fixing the analytic constants and an outer scale $X$, it uses one such set at $Z=\lfloor X^{C_t}\rfloor$. Its conclusion promises an eligible finite set across all qualifying field realizations and layers. [Published statement and use of exc](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/PartB.lean#L50-L83)

We reran this proof on a specified selector $E:\mathbb N\to\mathrm{Finset}(\mathbb N)$ and exponent $c$, using a proof of $\forall Z,\ \texttt{FirstBound}(\ell,R,c,L_0,Z,E(Z))$. The variant takes that evidence at the same place for every odd prime. It returns the additional equality $\mathrm{Exc}=E(\lfloor X^{C_t}\rfloor)$ beside the original cardinality and estimate. Every analytic premise in the original statement is present, including the scale and growth conditions on the evaluation point and the goodness condition on this very set. The quantitative conclusion, its transport to any other field realizing the base-field description, and its quantification over all specified layers are the original ones. [Prescribed selector theorem](PrescribedPartB.lean)

Of 95 lines in the pinned source, 89 are retained byte-for-byte in their original order. The private primitive-root lemma occupies identical source lines in both independently named Lean modules. The change names a new theorem, accepts $c,E$ and the all-cutoff bound, binds the chosen set directly, and returns its identity. The seven direct references to `point2`, `final`, `layerex`, `abiso`, `layeriso`, `shaInv_congr` and `vvat` occur in both elaborated proof bodies. The original contains a direct call to `exc`. The variant consumes the supplied bound and has no such call. [Diff and elaborated-call audit](results/prescribed_part_b.json)

A separate Lean control recovers the exact published type of `Win.partB` from the strengthened theorem. It calls `exc`, applies choice once to obtain a function of the cutoff, calls the new theorem and forgets its extra equality. Lean accepted this control with the standard three axioms.

The original and prescribed modules each passed individual kernel replay after checking all 649 project dependencies in the original closure, including the original endpoint itself, against pinned source blobs and the prior run's compiled-object hashes. The experiment used the pinned Mathlib binary cache. Its two modules share the prior build's library imports. To reproduce from a fresh [tower build](build_tower.py), use its single assembled library and output manifest in the command below. The runner checks the recorded source revision, package and compiler versions, and every original source and compiled-object hash in the Part B import closure. An incomplete closure is rejected.

```sh
python3 -B prescribed_part_b.py --source "$ORIGINAL" --toolchain "$LEAN_DIR" \
  --mathlib "$MATHLIB" --cache "$TRIAL/tower/lib" --manifest "$TRIAL/evidence/tower_build.json" \
  --work "$TRIAL/prescribed-part-b" \
  --out "$TRIAL/prescribed_part_b.json"
```

To reproduce with the [earlier bridge library](../joint-witness/REPRODUCE.md), omit `--manifest` and set `--cache` to that assembled library directory. The default authenticates the closure against the two published bridge-run manifests.

A prescribed run can expose membership for one chosen selector. To use the arithmetic estimate at a real evaluation point still requires its threshold and goodness hypotheses. In particular the finite filter at $Z=64$ alone supplies no such evaluation point. Fixing a selector in this variant supplies no equation for the separate witness originally selected by `thmBab_of`.
