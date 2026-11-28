# One exchange and the weighted orbit test

Can the exact coset counts of a retained arithmetic witness determine the weighted bad-orbit condition in the published source? A pair of sets gives opposite decisions even when both sets have the prescribed proportions, exactly 4/7 and 3/7, in a genuine two-coset frame. The comparison uses the source's inert prime class, Frobenius step, anchored marking pattern and weight at a test constant of one.

[LuaLaTeX manuscript](One_Exchange_and_the_Weighted_Orbit_Test.tex) · [Reproduce the evidence](evidence/README.md) · [Study design and timing](evidence/DESIGN.md) · [Host construction](evidence/HOST.md)

| Orbit size | Effect of one within-residue exchange | Bad-point count |
|---|---|---|
| 8,192 | A circular window goes from its cap of 2,112 to 2,113. There are no full tiles. | 0 → 4,049 |
| 32,768 | The sole tile loses a required point. The short-window maximum stays 1,071. This pair misses the lower density bound. | 0 → 6,339 |
| 131,072 | The sole marked tile among five loses a required point. Both sets satisfy the density bound. | 0 → 66,747 |
| 2^64 | The unique mark disappears while both sets have exact two-coset shares and satisfy the density bound. | 0 → 9,223,372,036,854,769,465 |

Three is the only eligible prime in the four hosts, with weight log(3)/3. Its Frobenius step generates the full orbit, so a failed local verdict charges every retained point. The 131,072-point set admits 1,043,238,003 one-point replacements preserving all counts modulo four. The 359,026,791 that touch the unique marked tile change the decision at the chosen budget. These are counts around the specified starting set.

Restoring the selected construction's rank bands gives a further result. At order 2^64 and epsilon=1/64, with prime 3 inert and generating a full orbit, the density floor and rank bands force mean short-window occupancy above 2,131.8. The allowed maximum is 2,112. This geometry therefore cannot give a locally good, dense orbit under those combined conditions.

Four finite outputs are reproducible with standard Python. Three Lean supplements separately check general orbit identities, host existence and Frobenius identification, and the window incidence bound. The specific numerical comparisons use source derivations and executable certificates. The full RH entry point was not rebuilt.

[Earlier public experiment](https://github.com/nousentllc/riemann-hypothesis/tree/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host) · [Original weighted predicate](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean#L36)
