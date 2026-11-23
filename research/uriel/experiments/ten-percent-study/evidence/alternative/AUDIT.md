# A 64-residue certificate covering every labeling

For every assignment of the numerical host labels there is a profile on the cyclic quotient of order 64 whose limiting direct-gain recovery fraction is at least **12087/120814**, approximately **10.004635%**. The profile gives the permitted residues and their rates. The original score is met by exact-count choices within these residues on sufficiently late arithmetic hosts. The previously selected existential mask and a finite arithmetic scale for attaining 10% remain unidentified. [Original-score and gain estimates](https://github.com/nousentllc/riemann-hypothesis/blob/a71afc29237a4b0ae379ff8be7d58310afb80d99/research/uriel/experiments/incumbent-recovery-study/evidence/rigidity/AUDIT.md)

## One threshold calculation

At each dyadic node let its width be w, its selected canonical-even and odd leaf counts be a,b, and its number of odd increments missing from all pair differences on that node be d. Doubling both the exposure and recovery units gives a numerator contribution 2bd and a denominator contribution bw for equal unit rates. Each selected leaf also contributes one tail unit to the denominator. The threshold surplus is ten times this numerator minus the denominator. Its node contribution is b(20d−w). If the two child supports are known only by size, both orientations of a pair can block at most two potential holes per pair, so d is at least max(0,w/2−2ab). The code also uses exact differences where indicated. Exact arithmetic transport comes from the preceding study; every constructed mask is shared by all its primes. [Phase and denominator](https://github.com/nousentllc/riemann-hypothesis/blob/f667dea291ef2a5b204810ad63611ef6b718b18a/research/uriel/experiments/recovery-frontier/evidence/search/SEARCH.md)

Split the root into its canonical even and odd halves E,O. Ignore any recovery at the root. In O keep just the minimum leaf of its canonical even child, OE. In its other child OO select k leaves among 16, ranked 0…15 by taking the canonical even child before the odd at each fork. Select 26−k leaves in E for the ordinary rule. All 27 retained residue classes have rate 64/27, in units of the original density. The fixed-size sampling then has exactly the original rounded total.

The 19-, 21- and 22-leaf dense reservoirs have unit threshold scores at least −195, −331 and −362. Use 16+3, 15+6 and 16+6 leaves respectively in their canonical children. The 16-leaf full node has score −256, and deleting its last rank gives −225. In a width-16 node, ranks 0,8,12 give score at least 157 by splitting 1+2 and then 1+1. The six-leaf local construction has score at least 86 for every labeling. Its three-case rule is given in the companion [hand audit](../hand/AUDIT.md). Subtract 32 times the odd child count to account for the dense half's own split.

Let H denote the unit score computed wholly inside OO. Let d now denote the missing generators of O. The whole-mask unit surplus is at least

~~~text
dense score − 65 + H + k(20d − 96).
~~~

Here −65 charges the singleton leaf in OE for its tail and its root-odd exposure, and 96 charges each OO leaf at widths 64 and 32. Each root and dense upper-level contribution neglected in this expression has nonnegative recovery.

## Seven tests for the reflection

In the 32-cycle of O, put OE's singleton at zero. Reflection exchanges OO's two eight-leaf children. It induces a permutation p of the eight canonical ranks between the two children. Each tree map preserves nested residue cosets and may swap the children of each node. Number its seven swap bits 0 through 6, breadth first, indexed by *input* prefixes; a 1 sends the canonical zero digit to a one. For a rank of three binary digits, obtain the output digits by XOR with the successive encountered swap bits. Thus all 128 permutations are covered. If k occupied OO leaves include l pairs matched under p, the exact number of missing generators of O is 16−2(k−l).

Find the first zero in the bit order 0,2,5,6,1,3,4. Select the row with that bit. L denotes the selected ranks in the first eight leaves and R the selected ranks in the second eight, before adding eight. The fourth column follows by applying p to at most four three-bit words. The last column is a lower bound on the unit surplus above.

| First zero | L | R | At least l | d at least | H at least | Surplus |
|---:|---|---|---:|---:|---:|---:|
| 0 | 0,1,2,3 | 0,1,2 | 3 | 8 | −73 | 115 |
| 2 | 0,4,5 | 0,1 | 2 | 10 | −57 | 67 |
| 5 | 0,4,6,7 | 0,1,2 | 3 | 8 | −95 | 93 |
| 6 | 0,4,5,6 | 0,2,3 | 3 | 8 | −95 | 93 |
| 1 | 0 | 0,4,5 | 1 | 10 | 50 | 39 |
| 3 | 0 | 0,4,6 | 1 | 10 | 48 | 37 |
| 4 | 0,1,2 | 0,4,6,7 | 3 | 8 | −111 | 77 |

For example, in the bit-5 row the previous bits 0,2 were both 1. Ranks 6 and 7 therefore map to 0 and 1 in some order. Rank 4 maps to 2 because bit 5 is zero. The three images are in R. Within OO every H in this table follows recursively using only the count bound on missing shifts. These rows cover 64+32+16+8+4+2+1 of the 128 possible p.

## The one remaining reflection

All seven ones means p(i)=7−i. Write the physical O coordinates of OO's first eight leaves as 1+4 rev(g(i)) modulo 32, where rev reverses the three binary digits and g is another tree permutation. An odd change of cyclic unit always gives this form with its first coordinate equal to 1. Reflection specifies the other eight coordinates. In the 16-cycle of OO they become

~~~text
x_i = 2 rev(g(i)),     x_(8+j) = −1−x_(p⁻¹(j))  modulo 16.
~~~

Normalization makes g(0)=0. Its free bits A,B,C,D have breadth-first indices 2,4,5,6. Use the first applicable line. Each has d=8. To check H, on each occupied node form its pair differences and count the absent odd increments. There are 8,4,2,1,1 normalized layouts in these rows respectively.

| Condition | OO ranks | Minimum H | Minimum unit surplus |
|---|---|---:|---:|
| A=1 | 0,8,9,12 | 178 | 7 |
| C=0 | 0,4,8,10,11 | 89 | 13 |
| B=0 | 0,8,10,12 | 176 | 5 |
| D=1 | 0,8,12,14 | 248 | 77 |
| Otherwise | 0,8,12,14,15 | 57 | use weighted rates |

The code verifies every normalized row and the equality of the score under all eight odd scalings giving the unnormalized layouts. The [saved table](results.json) gives the physical coordinates for all sixteen normalized layouts. The final row has bits 0110. Giving each of its 22 dense leaves rate 411/176, the OE singleton rate 3/4, and its five OO leaves rate 19/8 gives total rate 64. The dense doubled numerator is at least 20 per unit rate and its doubled denominator at most 562. The singleton contributes denominator 65. The five OO leaves contribute numerator at least 96 and denominator 583. Thus the full numerator is at least 12087/44 and the denominator at most 60407/22. Their ratio is 12087/120814. Its threshold surplus is 14/11. The ordinary rows all exceed this fraction since they have unit surplus at least 5, physical rate 64/27 and doubled denominator at most 64·127. The worst-case lower bound has no optimality claim.

## Original score and independent replay

Each occupied class is sampled at a fixed count rounded from its prescribed rate times the original density and class population. A bounded rounding adjustment enforces nearest-integer total size. An eligible orbit traverses its projected coset in a fixed periodic order. In an original cell the mean total and even-site inclusion probabilities converge to the respective node sums of rates divided by node width, called μ and ν. The full leaves and finer levels have ν=μ/2. The marked-tile test passes when the geometric factor exp(−μ)ν^(3r/(6r+1)) exceeds 1/10. The verifier checks 100ν>exp(2μ) when ν≤1 and 10¹³ν⁶>exp(13μ) when ν>1; these suffice for every original r≥2. It checks 57 distinct pairs using rational Taylor upper enclosures and includes all three possible dense six-leaf patterns. The bounded rate cap 19/8 suffices for the original long and short windows. The previous fixed-count, anchored comparison applies to this fixed number of strata, giving expected bad mass o(M) at the same original bad-mass scale. Its cardinality term tends to zero; the original independent-law mean is at least (1−δ)/2. [Original score](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173) · [Original mark predicate](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26)

Run `python3 -B verify.py --check` from this directory. The run covers 16,384 sparse relative layouts and the hand construction applies to every independent dense labeling. In the difficult weighted row the best of the four ordinary reversal menu masks has negative surplus as a control. The original incumbent and the global RH endpoint were not evaluated by this finite verifier.
