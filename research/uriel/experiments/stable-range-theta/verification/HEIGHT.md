# A real exponent in the dyadic height argument

The source module `Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount` proves that a measurable, strictly positive function $f$, bounded above by $R\ge1$, has all sufficiently large powers integrable if its dyadic superlevel sets obey

$$
\mu\{f\ge 2^{-j}\}\le Cb^j,\qquad j=0,1,2,\ldots,
\qquad C<\infty.
$$

The original proof picks an integer $k$ satisfying $2^{-k}<1/(b+1)$. What actually enters the sum is $b2^{-t}$. In `DyadicThreshold.lean`, `integrable_of_count_at` proves the conclusion for every $t\ge t_0\ge0$ as soon as $b2^{-t_0}<1$. It uses the original cover by shells $2^{-j}\le f\le2R2^{-j}$ and the original termwise integral bound. The only change relevant to the estimate is how the ratio is placed strictly below one.

Taking $b=2^\alpha$ gives integrability for every real $t>\alpha$ by `integrable_power_after`. For the exponent $\alpha=1+8Dn^2$, `quarter_gap` gives $\alpha+1/4<d/2$ if $d\ge3+16Dn^2$. This is the smallest integer $d$ for which an open interval $\alpha<t_0<d/2$ exists. The original, more conservative margin also holds at $k=\alpha+1$ by `ratio_at_integer`. These statements control the height step conditionally on the superlevel estimate. The replay supplies neither an automorphic representation nor a dimension bound meeting the other lift hypotheses.

**Why strictness matters.** For the abstract measure hypotheses, take $b>1$, $G=\mathbb N$, $f(j)=2^{-j}$, and assign the point $j$ mass $b^j$. Then the mass of the $j$-th superlevel set is $1+b+\cdots+b^j\le b^{j+1}/(b-1)$, and the integral of $f^t$ is exactly the sum of $(b2^{-t})^j$. At $t=\log_2 b$, every term is one. This mathematical counterexample establishes sharpness for the abstract data. The Lean file formally checks the sufficient bound and the arithmetic gap. Realizing the example in an automorphic geometry would be a separate claim.

**Replay.** From the verification folder, use the pinned Lean 4.33.1 SDK and a built Mathlib checkout at commit `0df444a360eaa60ab8c11dca51a86af692955474`. In the command below the three shell variables name the SDK root, Mathlib checkout, and local research Git checkout containing the pinned source object.

```sh
python3 -B replay_height.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --git "$RESEARCH_CHECKOUT"
```

The check authenticates the original source blob, builds and replays the entire original module with its sole import `Mathlib`, verifies the unchanged proof spans, builds and replays the new lemmas, and checks the axiom reports. The six reported declarations depend on `propext`, `Classical.choice` and `Quot.sound`. The commands use cached Mathlib objects. The exact replay record is in `height_receipt.json`.
