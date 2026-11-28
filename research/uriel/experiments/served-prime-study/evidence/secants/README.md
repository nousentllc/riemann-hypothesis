# Finite secant bounds for prime mass

Let $`F(t)=\sum_i w_i(t-n_i)_+ + \beta t`$ on a finite set, with $`w_i\ge 0`$. At a cutoff $`H\ge 0`$, write $`M_< = \sum_{n_i<H}w_in_i`$ and $`M_\le = \sum_{n_i\le H}w_in_i`$. For $`h>0`$, the supplement proves the two outside bounds
```math
 H\frac{F(H)-F(H-h)}h-F(H) \ \le\ M_<\ \le\ M_\le\ \le\
 H\frac{F(H+h)-F(H)}h-F(H).
```
The middle relation follows from the nonnegative weights and $`H\ge0`$. The Lean declaration `cumulative_bracket` gives the leftmost and rightmost inequalities in a form multiplied by $`h`$. This handles $`h=0`$ without division. The endpoints $`n_i=H`$ can contribute to the inclusive mass. The proof treats this boundary explicitly and allows any fixed common linear term $`\beta t`$.

## Where the bracket loses precision

Subtract the lower bound from the upper one. The full width at $`h>0`$ is exactly
```math
 \frac{H}{h}\sum_i w_i\max(h-|n_i-H|,0).
```
Atoms at distance $`h`$ or more contribute zero. An atom at the cutoff contributes $`H w_i`$ however small the positive width $`h`$ becomes. The slope term $`\beta`$ cancels exactly. The width identity alone allows signed weights; the enclosure requires the positive measure assumption. For the arithmetic application, one sets $`w_i`$ to the nonnegative projected von Mangoldt weight divided by its positive index. Recovering a sharp prime asymptotic additionally requires mathematical hypotheses on the data used to control $`F`$. A bound on a single ordinate by itself supplies neither secant.

For integer indices and an integer cutoff, any width $`0<h\le1`$ leaves only atoms at $`H`$ inside this triangular window. Its width then equals $`M_\le-M_<`$, forcing the lower and upper estimates to equal their respective strict and inclusive masses when the three values of $`F`$ are exact. If each supplied value has absolute error at most $`E`$, a common upper bound on the absolute error of either derived value is $`(2H/h+1)E`$ by the triangle inequality. These are deductions from the displayed identities.

## Replay

`PrimeMassSecants.lean` imports Mathlib and introduces no assumptions about the Riemann Hypothesis. The three-point inequality, its one-atom left and right bounds, the one-atom triangular identity and the finite width identity are independently spelled out in that module. The source was compiled with the pinned Lean 4.33.1 toolchain and original Mathlib package revisions. The separate `leanchecker` replay and the five axiom audits are in `verification.json`. Mathlib objects and the compiler are trusted local inputs. The commands do not rebuild the original RH entry point.

Prepare the helper checkout, compiler and Mathlib build as in the [original experiment replay instructions](https://github.com/nousentllc/riemann-hypothesis/blob/9ac7e1b546b132edde02709e1c0af1bfccd40755/research/uriel/experiments/retained-host/REPRODUCE.md). From this directory run

```sh
python3 -B replay.py --checkout "$CHECKOUT" --toolchain "$LEAN_ROOT" --mathlib "$MATHLIB" > verification-local.json
```
