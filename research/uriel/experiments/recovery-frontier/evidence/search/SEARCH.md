# How close can a sixteen-residue design get?

In the sixteen-residue profile class defined below, a fixed raw conductor-one host with *any* orientation admits a source-compatible construction recovering at least
\[
 \frac{46\,000\,000}{700\,425\,363}=6.567437793\%
\]
of its local allowance asymptotically. The best guarantee uniform across orientations in this profile class is at most \(23/348=6.609195402\%\). The interval has width \(0.041757610\) percentage points. If the orientation is favorable, the equal-rate panel attains \(24/115=20.869565217\%\). The latter is an existence result on some combinatorial labelings. A uniform guarantee must work even on the weakest orientation.

## Scope and objective

Write \(a_t\) for the limiting inclusion-rate multiplier on residue \(t\in\mathbb Z/16\), and use the fixed support \(S=\{t:a_t>0\}\). The quantitative cap in this panel is \(a_t\le 23/10\), and \(\sum_t a_t=16\). The original inclusion scale is \(\delta\). In each residue stratum sample uniformly at a fixed count nearest to \(a_t\delta n/16\), distributing at most finitely many rounding adjustments so the total is nearest to \(\delta n\). Only fixed positive rates are used as \(x\) increases along a specified orientation. The allocation is chosen after the raw labeling is known and before selecting any top. The assertions concern realizations concentrating around the fixed profile with sufficient first edges wherever the support permits them. An upper bound for this fixed-rate geometric design does not bound rare masks under an arbitrary probability law or masks with unrestricted structure.

Every dyadic node \(v=c\bmod 2^j,\ 0\le j<4\), has two children. The least numeric label in the real host fixes which child is even. All \(2^{15}\) choices of those preferences occur in a suitable labeling. For example, sorting the leaves lexicographically with the preferred child first suffices. Affine coordinate transformations \(t\mapsto ut+b\bmod16\) for odd \(u\) preserve step weights, occupancy and these preferences after transporting them. The enumeration explicitly partitions the 32,768 orientations into 256 orbits of size 128.

At a node of quotient width \(w=16/2^j\), define \(d_v\) as the number of its \(w/2\) odd step residues for which its supported leaves have no adjacent pair in either orientation. Each such step residue has full-group frequency \(1/16\). Write \(b_v(t)=1\) on the canonical odd child of \(v\) and zero elsewhere. The limiting exposure at deeper levels averages \(1/32\) on each uniformly sampled leaf. Uniform prime-step weights, and the within-leaf score and edge-count concentration established by the preceding study, convert these frequencies to the asymptotic ratio
\[
 \frac{\mathcal R_x}{\mathcal K_x}\ \longrightarrow\
 \frac{\sum_t a_t\,\sum_v 2d_v b_v(t)}
 {\sum_t a_t\,[1+\sum_v w b_v(t)]}.
\]
The formula retains both directions of adjacency. Below the four displayed levels, every occupied stratum is filled at a fixed positive rate; these levels contribute the denominator tail. There is no persistent structural hole within a filled stratum. [Original gain transport](https://github.com/nousentllc/riemann-hypothesis/pull/11) · [Fixed-size selection and directional recovery](https://github.com/nousentllc/riemann-hypothesis/pull/12)

For clarity, the original-window argument generalizes as follows. For each fixed oriented node let \(\mu=\sum_{t\in v}a_t/w\) and \(e=\sum_{t\in v,\ t\text{ even}}a_t/w\). On deeper occupied leaves these become \(a_t,a_t/2\). A cell's empty probability under independent marginal trials tends uniformly to \(\exp(-\mu)\), and its even-singleton probability tends to \(e\exp(-\mu)\). Requiring both to exceed \(1/10\) suffices for a marked tile. The weaker paired test used here is
\[
 e^{-\mu}>1/10,\qquad e\,e^{-2\mu}>1/100 ,
\]
where the standalone \(e\) in the second product denotes the even-site mean. There are \(3r+1\) empty cells and \(3r\) even-singletons per mark, so these two strict inequalities suffice with a positive margin. The code uses only rational Taylor upper/lower enclosures for the comparisons. Strata with no supported point never incur anchored good-orbit charges. The fixed-shell cylinder likelihood bound is \(1+o(1)\) on all source windows since the finite strata have size \(n/16\). The anchored short-window bound remains \(O(\delta^K+L\delta^{K+1})=o(x^{-2})\). Long-window failure uses a rate bounded by \((2.3+o(1))\delta\), so its union-bound base stays strictly below \(1/2\). Consequently the bad mass is \(o(M)\) with probability tending to one along suitable thresholds. The count term is \(o(1)\), while the original uniform expectation is at least \((1-\delta)/2\).

For the exact ratio, each geometrically allowed orientation has at least \(L/16\) permitted disjoint edges at long orbit length \(L\). Both endpoints have rates bounded below by a positive profile-dependent constant times \(\delta\). The exponential matching tail survives conditioning on finitely many modal counts. Every long orbit admitting either orientation therefore has negligible recovery in the prime interior from the preceding study. The remaining ones recover their odd offset mass to leading order. The lightweight geometric and numeric tests do not build this global transport in Lean.

## Enumeration and upper certificate

| Panel | Worst orientation's best | Best individual orientation |
|---|---:|---:|
| Homogeneous support, single-cell test | 4/67 | 24/115 |
| Homogeneous support, paired test | 4/67 | 24/115 |
| Ternary rates 0, 1, 2, single-cell test | 2/39 | 1/12 |
| Ternary rates 0, 1, 2, paired test | 1/19 | 8/93 |
| Closed-box relaxation | 23/348 | 137/654 |

All 65,536 supports are considered before feasibility and zero-objective pruning. Because \(16(10/23)>6\), a feasible support has at least seven leaves. At a nonempty supported node some canonical even site is necessary for a mark. If a node with both parities supported has no missing step, its contribution to the numerator vanishes. One-child nodes must choose the supported child as even. After these checks, 8,256 supports can matter and 119,424 ternary rate vectors on those supports have total mass 16. Independent direct step counting checks every returned rational certificate.

For the upper relaxation, fix the original support and retain the minimum requirement of some eligible even site in each occupied node, dropping quantitative mark inequalities. For each orientation the numerator and denominator are linear in \(a_t\) on that support. Relax rate positivity to a closed box on those leaves, keeping the support geometry itself fixed. A linear-fractional maximum with strictly positive denominator occurs at a vertex. A vertex assigns six leaves \(2.3\), one leaf \(2.2\), and the remainder zero. For a trial ratio \(z\), sorting coefficients of numerator minus \(z\) times denominator and filling the box by descending coefficient maximizes that difference exactly. An improving vertex strictly increases the rational quotient and the finite process stops when no improving vertex exists. Closure can assign zero mass to an assumed supported leaf; these points certify upper bounds and need not satisfy the original score.

At orientation 64 the maximizing relaxed value is \(23/348\). At this orientation one certified attaining lower profile has support \(\{0,1,2,4,7,8,10,12\}\). In this order its rates are \(2.3,\ 0.1475121,\ 2.3,\ 2.3,\ 2.3,\ 2.3,\ 2.0524879,\ 2.3\). These exact decimal rationals sum to 16. The other weak orientations and their rational certificates are listed in the refinement record. Initial homogeneous or ternary certificates already exceeded \(23/348\) on the remaining orientations. The upper bound uses a weakest possible orientation, not a claim that every particular labeling has a small ceiling. Current knowledge of the arithmetic host does not supply a more favorable labeling.

## Reproduce

From this directory run the following with Python 3.11+ and a C++17 compiler. The default compiler is c++; set CXX to select another. Both the exhaustive search and final feasibility checker use the Python standard library and the compiled enumerator.

~~~sh
python3 -B run_search.py --check
python3 -B refine.py --check
~~~

Running refine.py without the flag repeats the bounded coordinate-search heuristic. Its search floats guide candidate generation only. The --check mode verifies the stored rational witnesses independently of that heuristic. Running run_search.py without --check regenerates its exhaustive result. [Design](DESIGN.md) · [Registered refinement](REFINEMENT.md) · [Exhaustive certificates](results.json) · [Continuous-rate certificates](refinement.json)
