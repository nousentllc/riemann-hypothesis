# Where the size condition first becomes possible

The registered pair fails the cohomological size condition by hundreds of natural-log units. We asked post hoc whether a better prime search at the same scale could fix it. For the two specified inequalities, the entire pair of prime boxes is already excluded there.

Write the prime-selection scale as $T=X^{1/J}=2^k$ and take $\varepsilon=1/64$ as in the registered run. With $u=\log T$, the source's strict lower and weak upper bounds for the logs of $q,d$ give

$$\tfrac12(1+u^2)e^{u/320}<\log(qd)\le (1+u^2)e^{u/320}.$$

The scalar cohomological condition used in the comparison is $\log(qd)\le X^{\varepsilon/(4J)}=e^{u/256}$. Dividing by this ceiling leaves $r(u)=(1+u^2)e^{-u/1280}$ at the upper end of the boxes and $r(u)/2$ at the lower end. [Prime boxes](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L27-L37) · [Cohomological condition](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L40-L49)

| Integer $k$ in $T=2^k$ | Consequence of the boxes alone |
|---|---|
| $48$ through $36{,}126$ | Every pair in the boxes exceeds this cohomological ceiling. |
| $36{,}127$ through $37{,}549$ | The ceiling lies inside the interval allowed for the sum of the logarithms. Prime existence and the other constraints are separate questions. |
| $37{,}550$ and above | Every pair in the boxes meets this one ceiling. |

For $u>1$, the logarithmic derivative $2u/(1+u^2)-1/1280$ decreases strictly, so $r$ can have only an interior maximum there. Both $k=48$ and $k=4096$ have $r>2$. At $k\ge4096$, $u>2560$ and the derivative is negative. We used rational enclosures of natural logarithms and binary search on this decreasing branch, checking both adjacent integers at each crossing. Logarithms reduced to $1\le z\le2$ use 24 terms of the atanh series and a geometric upper bound on the remainder. The code stores outward-rounded signed residuals in units of $10^{-12}$. [Exact calculation](box_threshold.py) · [Boundary certificates](results/box_threshold.json)

These cutoffs apply to this dyadic slice and this choice of $T,X,J$. They quantify one obstruction independently of the supplied exceptional labels. The eventual thresholds for field construction, cohomology and analytic estimates still require their own inputs.
