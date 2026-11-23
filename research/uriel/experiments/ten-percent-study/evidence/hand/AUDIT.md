# The final eight label configurations reduce to one calculation

This is the correction that clears the 10% threshold for the eight configurations where uniform rates were insufficient in the primary construction. All rates below are in units of the original density δ. At a node of width w let d be the number of missing odd increments and o the odd-child mass in rate units. Use 2do as its gain numerator and wo as its exposure denominator. Each unit of retained leaf rate also adds one unit to the denominator for the finer dyadic tail. The comparison 10 times numerator minus denominator thus adds (20d−w)o per node and subtracts each leaf rate once. It suffices to lower-bound the numerator. The conversion to the original prime weights and same-mask direct gain uses the source-derived asymptotic estimates of the preceding experiment. [Direction weights and recovery transport](https://github.com/nousentllc/riemann-hypothesis/blob/f667dea291ef2a5b204810ad63611ef6b718b18a/research/uriel/experiments/recovery-frontier/How_Much_of_the_Odd_Allowance_Can_Return.pdf)

## A 22-leaf reservoir every labeling admits

The canonical even half E has 32 leaves. Fill all 16 leaves in its even child. Use six leaves in its odd child. These six can always be chosen with local threshold score at least 86 in unit weights.

Within the 16-leaf node take its minimum as the sole supported even leaf. Label the eight odd leaves by canonical binary traversal j=0,…,7, always taking the preferred child first. Their internal exposure costs are 1+2j, including each leaf’s tail, so the eight costs sum to 64. Reflection around the minimum pairs leaf i in the first four with leaf 4+p(i) in the second four. Here p preserves the four-leaf binary tree because reflection is affine with an odd multiplier. Apply the following deletion rule.

| Condition | Three odd leaves to delete |
|---|---|
| p(3)≥2 | 3, 6, 7 |
| p(3)=1 | 3, 5, 7 |
| p(3)=0 | 1, 6, 7 |

In the third row p(1)≥2 since 1 and 3 lie in different two-leaf children. Each row removes a reflected pair, gives a nonempty canonical even child in every surviving node, and removes canonical ranks summing to at least 14. At least two generator increments are therefore blocked. The remaining five costs sum to at most 64−3−28=33. The six-leaf numerator is at least 2·2·5=20 and its denominator at most 1+16·5+33=114. The full 16-leaf child contributes denominator 256. The width-32 split adds 32·6=192. Together E has numerator at least 20 and denominator at most 562 in unit weights. Its threshold score is at least −362.

## A single sparse pattern for the eight remaining cases

In the canonical odd half O keep only its minimum leaf in its even child OE. Within OO number the 16 leaves by canonical traversal and retain ranks 0, 8, 12, 14, 15. In a representative exceptional layout these have physical coordinates 0, 1, 11, 7, 15 in the 16-cycle. All eight layouts follow by applying z ↦ (2b+1)z+b modulo 16, for even b. These maps preserve differences up to a unit and commute with the reflection z ↦ −1−z. The [exact output](results.json) lists all eight coordinate maps for comparison with the primary coverage certificate.

The reflected partners of the five ranks have a union of size eight with those ranks since the pair 0 and 15 occurs in both sets. Thus eight of the 16 generator directions of O are blocked. Within OO the missing increments on the 16-cycle are 3 and 13, and four of the five ranks are odd there. All smaller nodes have either zero odd exposure or no missing step. For the three smaller nodes with odd exposure, the pairs (width, odd count) are (8,3), (4,2), (2,1). The OO score inside its own subtree is 4(20·2−16)−8·3−4·2−2·1−5=57. Including O's eight blocked steps and the outer odd cost gives 57+5(20·8−32−64)=377. Equivalently the numerator is 96 and the denominator 583. The OE singleton has no internal odd exposure before the leaf tail and pays 64 at the outer root, for denominator 65. These are sufficient contributions; any additional recovery elsewhere increases the result.

## Exact weighted inequality

Assign E leaves rate 411/176, the OE singleton 3/4, and the five OO leaves 19/8. Their rates sum to 64. Rounding stratum counts at the host scale gives exact nearest target cardinality. At the limiting profile the certified fraction is at least

~~~text
 [20(411/176) + 96(19/8)] / [562(411/176) + 65(3/4) + 583(19/8)]
 = 12087/120814 = 10.004635224...%.
~~~

The threshold margin is equivalently (19/8)377 − (411/176)362 − (3/4)65 = 14/11. At a finite host the small terms in the arithmetic transport still have to decay. This is a leading-order certificate.

## Short checks for the original mark predicate

On a node of uniform positive rate c, write a for its canonical-even occupied fraction of all its leaves. Total occupation is at most a+1/2. The paired mark factor is bounded below by

~~~text
 exp(−c(a+1/2)) min((ca)^(1/2), (ca)^(6/13)).
~~~

For the source tile integer r≥2 this lower-bounds the per-cell geometric mean of its required empty-cell and even-singleton probabilities. Its log is concave in a, so at widths up to 16 a nonempty preferred child suffices once a=1/16 and a=1/2 pass. Both endpoints exceed 1/10 at c=411/176, 19/8 or 64/27. The verifier establishes the exponential comparisons by rational enclosure. For the homogeneous rate 64/27 this criterion also handles width-32 even count at least two. At even count one the threshold is crossed exactly between occupancy counts 13 and 14, from  exp(52/27) < 200/27 < exp(56/27). At the root, occupation 27 needs at least two preferred leaves, because 2/27 > exp(2)/100. 

For the exceptional weighted construction, in O the total cell mean is 101/256 and the even mean 3/128. Here exp(101/128) < 75/32. In E, 16 of 22 occupied leaves are even. Along the OE minimum's path all occupied leaves are canonical even until the uniform leaf tail. These give strict margins for the actual tile. The uniform positive rates are at most 19/8; the prior fixed-count short and long window estimates apply. The original uniform expectation and original bad-mass constants are used to judge this mask. [Original marking rule](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SubspaceCounting/GoodOrbitIntervalTileCondition.lean#L9-L26) · [Original score](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThickFrames/select.lean#L70-L173)

Run `python3 -B verify.py --check` from this directory. The checks cover the eight dense matchings, the eight sparse layouts, their direct step counts and rational mark inequalities. The primary coverage argument identifies which labelings reach this final case.
