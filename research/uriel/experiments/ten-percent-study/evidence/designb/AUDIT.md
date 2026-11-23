# What a 32-residue construction can guarantee

We tested both the lower certificate for a fixed mask and an upper relaxation over all stationary 32-residue profiles with maximum rate multiplier 12/5. Throughout this note the geometric recovery formula assumes sufficiently many realized edges in each permitted orientation on long orbits, as in the previous fixed-class sampling argument. It does not constrain arbitrary correlated masks with the same class counts. [Original score and gain transport](https://github.com/nousentllc/riemann-hypothesis/blob/f667dea291ef2a5b204810ad63611ef6b718b18a/research/uriel/experiments/recovery-frontier/evidence/search/SEARCH.md)

## A positive certificate checkable without code

Take an ordering with canonical even child $c\bmod 2s$ at each node $c\bmod s$. The support is the fourteen residues $0,1,\ldots,13$ modulo 32. Each occupied class has rate $(16/7)\delta$, with bounded rounding to keep the total nearest $\delta n$. At a node let $D$ be the number of its generator residues for which no two support points differ by that residue in either orientation. If $b$ occupied leaves lie in its canonical odd child and its width is $w=32/s$, the gain numerator receives $2Db$ and the exposure denominator receives $wb$. The fine-level uniform tail adds 14 to the denominator. All fourteen rates are equal, so they cancel.

| Stride $s$ | Total $2Db$ | Total $wb$ |
|---:|---:|---:|
| 1 | 28 | 224 |
| 2 | 24 | 96 |
| 4 | 8 | 48 |
| 8 | 0 | 24 |
| 16 | 0 | 0 |

For example the whole interval misses odd residues 15 and 17 and has seven odd leaves. Each parity orbit is a seven-point interval on a 16-cycle missing two generator steps and having three odd leaves. Subcycles of length eight contain either three or four consecutive positions. Only the two three-point intervals miss generators (two each). The remaining rows follow from the lengths in each residue. The recovered fraction is $60/(392+14)=30/203$, or 14.7783%.

For the original mark test, write $\mu$ for the cell's total mean and $\nu$ for its mean on even sites. Every occupied node is a prefix interval of its subcycle. It has at least half of its occupied points on the canonical even side. Across all occupied heights and full leaf tails, $4/7\le\mu\le16/7$ and $\nu\ge\mu/2$. Both $e^{-\mu}$ and $\nu e^{-\mu}$ exceed $1/10$. For the latter it suffices to check the two endpoints of $(\mu/2)e^{-\mu}$, since its sole interior stationary point is a maximum. The former follows from $e^{16/7}<10$. These strict margins suffice for the original disjoint tile trials. The bounded rate also preserves the earlier short/long window and fixed-count cylinder estimates. The root count is exact to rounding; the score tends to zero on a suitable sequence of realizations. This is a witness for the displayed ordering. Other canonical orders can place a surviving lone child on the odd side.

## Complete homogeneous search with an odd generator missing

Each allowed support in this panel has at least 14 leaves, since all rates are at most $12/5$ with sum 32. If an odd generator $h$ is missing, the support is an independent set of the 32-cycle ordered in steps of $h$. It has at most 16 leaves. Enumerating every independent set of sizes 14, 15 and 16 in each of eight distinct unsigned odd directions gives 43,474 distinct supports after deduplication. Give each of the $k$ occupied leaves rate $32/k$. In every node test the sufficient marked-tile inequality $100\nu>e^{2\mu}$ for $\nu\le1$ or $10^{13}\nu^6>e^{13\mu}$ for $\nu>1$, valid for source tile parameter $r\ge2$. Strict signs are verified with rational Taylor enclosures. This uses the previously proved transfer of these local margins through the actual selector's count and window score. [Fixed-count and tile derivation](https://github.com/nousentllc/riemann-hypothesis/blob/f667dea291ef2a5b204810ad63611ef6b718b18a/research/uriel/experiments/recovery-frontier/evidence/profiles/AUDIT.md)

A bottom node with one supported child forces that child to be even. With two supported children both choices give the same exposure because their rates are equal. Once the 15 upper-tree orientations are fixed, a candidate therefore covers a Boolean subcube of the 16 remaining orientation bits, and its ratio is constant on that subcube. The 32,768 upper-tree words split into 256 equivalent classes of size 128 under $t\mapsto ut+d\bmod16$ with $u$ odd. These maps lift to bijections on the 32-residue cycle and preserve the number of covered bottom assignments. The search covers 16,444,252 out of 16,777,216 representative configurations at threshold $1/10$, or 2,104,864,256 of all 2,147,483,648 label words. This 98.01538% is a count of orientations admitting an example, distinct from recovered allowance fractions. The other 42,619,392 words require another construction or a better analysis. The displayed root-hole coverage is exact for these presets and this sufficient mark test.

## A rigorous adverse example for the rate-capped geometric method

The bit numbered $s-1+c$ in a word tells which child is even at node $c\bmod s$: child zero is $c\bmod 2s$, child one is $c+s\bmod2s$. Take the word **8,421,923**. One can realize any such tree of minima by listing all leaves of the preferred child before the other child, recursively. Exhaust all supports consistent with having an occupied even child at every occupied node. Each half-tree has 1,807 possible supports including the empty set: at a node the admissible count obeys $b'=1+(b-1)b$ starting with $b=2$ on a leaf. After imposing the root condition and at least fourteen leaves, exactly 3,024,572 supports remain.

For each support and retained leaf $t$ its coefficients are
\[
 R_t=\sum_{\text{odd ancestors of }t}2D,\qquad
 K_t=1+\sum_{\text{odd ancestors of }t}w .
\]
A rate vector $a_t$ has fraction $\sum a_tR_t/\sum a_tK_t$. To bound it above at $A/C$, maximize $\sum a_t(CR_t-AK_t)$ on a closed box $0\le a_t\le12/5$, $\sum a_t=32$. Closing the box relaxes support positivity. Drop the quantitative mark inequalities too. At a maximizing vertex thirteen coefficients receive $12/5$, the next receives $4/5$, and the rest receive zero. Folding over all supports gives the following integer maxima (objective multiplied by five).

| Threshold $A/C$ | Maximum | Strictly above | Tied |
|---:|---:|---:|---:|
| $1/10$ | $-48$ | 0 | 0 |
| $6/61$ | 0 | 0 | 2 |

Thus the exact relaxed maximum for this word is $6/61=9.83607\%$. A reader can check the lower, attaining vertex directly. The occupied leaves are $\{1,3,4,5,6,7,9,11,13,16,17,21,25,29\}$. Leaf 6 receives $4/5$ and all others $12/5$. Only leaves 4, 7 and 16 have positive numerator, respectively 12, 4 and 8. Multiplying all weights by five yields numerator 288 and denominator 2,928. The exhaustive upper portion is a computer-assisted certificate; the supplied small program recomputes it. No claim is made that the vertex passes all the dropped quantitative conditions. Allowing arbitrarily high intensities, larger periods or additional within-class correlations invalidates this upper-bound scope.

The adverse word was discovered after inspecting the first uncovered configurations from the cycle test. Starting from word 33,315, a one-bit perturbation produced 8,421,923. The adverse datum was then frozen and checked at the conjectured rational optimum. The input file records the initial tests separately. The scripts verify all finite thresholds with integer comparisons and independently evaluate the rational vertex by literal differences. Run `python3 -B run.py --check` in this directory with a C++17 compiler. [Original design and refinement](DESIGN.md) · [Results](results.json)
