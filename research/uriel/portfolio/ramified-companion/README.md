# The ramified companion fiber

Let `O = Z₂[π]` with `π² = 2`, and normalize additive Haar measure by `μ(O) = 1`. In the six scalar coordinates of the original rank-three Gaussian lattice write `Q(x) = Σ xᵢ²`. For $d\geq 1$, let $N_d(t)$ count the solutions of $Q(x)\equiv t\pmod{\pi^d}$ in $(O/\pi^d)^6$, and let $\rho_d(t)=N_d(t)/2^{5d}$.

**Written conclusion.** For $k\geq 1$ and an integral unit $u$, at $t=4^k(1+\pi)u^2$ the normalized count is $2-2/256^k$ at every depth $d\geq 4k+2$. It is $2$ at $d=4k+1$. Applying the original regular-fiber comparison yields the same value $2-2/256^k$ for the original lattice mass at the named place. The all-depth and transport arguments below are written deductions. The new Lean module checks the modulo-two obstruction.

## The first lift

Write $c=1+\pi$. For any $d\geq 6$, no solution at $4c$ can have all six entries divisible by $2$. Otherwise division by $4$ in the equation would give $Q(y)\equiv c\pmod{2}$. Every square $(a+b\pi)^2$ has π-coefficient $2ab$, while $c$ has coefficient $1$. The new module `CompanionObstruction.lean` checks the corresponding residue obstruction in the inherited ring, and its completed-order consequence. Lean 4.33.1 compiled the module, and the standalone checker replayed it. The axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Thus only two strata survive at the base target $4c$. A primitive tuple has at least one coordinate in $O^\times$. The inherited pivot permutation moves such a tuple's value by any prescribed element of $(\pi^5)$, preserving primitivity. For a fixed target modulo $\pi^5$, each primitive tuple lifts in $2^{6(d-5)}$ ways, and the permutation divides those lifts equally among $2^{d-5}$ target classes. The normalized primitive contribution is constant once $d\geq 5$. This applies to the primitive stratum at $4c$ and to the residual primitive stratum at $2c$ after dividing all coordinates by $\pi$. The latter has residual depth $d-2$, so both strata are stable for $d\geq 7$.

To connect depths 6 and 7, the residual target $2c$ must be lifted from modulus $\pi^4=4$ to modulus $\pi^5$. Every representation modulo $4$ has a nonunit coordinate. For a unit $a+b\pi$, the difference between the scalar coefficient and the π-coefficient of its square is $1\bmod4$. Six unit squares would give difference $6\equiv 2\bmod4$, but $2c$ has difference zero. Add $2$ to the first nonunit coordinate $y$. It stays a nonunit, and the square changes by $4(y+1)\equiv 4\pmod{\pi^5}$. Subtracting $2$ in the same coordinate is the inverse. The map pairs the two target children, preserving the primitive stratum. Across all coarse tuples, the two target children divide the lifts equally. Each receives $2^5$ times the coarse count, matching the denominator gain. The normalized residual count therefore also stays constant at this step.

The inherited `RamDilate.companion_count` gives $N_6(4c)=2{,}139{,}095{,}040$, hence `255/128`. Independent direct histogram convolution and the earlier transform agreed on the full count tables at the depths used in this check. The base ratios from depths 5 to 9 are $2,255/128,255/128,255/128,255/128$. At depth 9 the contributions by minimum valuation 0, 1 and 2 are $15/8,15/128,0$.

## Scaling and the named-place measure

For $j\geq 3$ and depth $d\geq 2j+2$, the target $2^jc$ is zero modulo $\pi^5$. The normalized primitive count for that residue is $15/8$. On the stratum with all coordinates divisible by $\pi$, writing $x=\pi y$ gives the residual target $2^{j-1}c$ at depth $d-2$. There are $2^6$ extra input lifts, while the normalized denominator gains $2^{10}$. Thus

```text
rho_d(2^j c) = 15/8 + rho_(d-2)(2^(j-1) c)/16.
```

The recurrence fixes $2$. Its $2k-2$ applications from $j=2k$ reduce the deficit $2/256$ to $2/256^k$. Multiplying each coordinate by $u$ is a permutation in every quotient, so it preserves the counts for the target multiplied by $u^2$. At the immediately preceding depth, $4^kc u^2$ and $4^k u^2$ are congruent, and the inherited square-family predecessor has ratio two.

Each target ball has Haar mass $2^{-d}$, and its preimage in the integral six-coordinate lattice has product Haar mass $N_d(t)2^{-6d}$. The cofinal coefficient balls thus give the positive finite tube ratios required by `RamTransportForm.original_mass`. Pulling back these balls and the six coordinates under `RamPlaceCompletion.e` gives the original measure on the original lattice. The transfer applies to every standard normalized Haar measure and every admissible fiber family.

## Replay

Run `python3 -B check_counts.py | diff -u counts.json -` in this directory. This exact-arithmetic control covers depths 5 through 9 at the first scale, depths 9 and 10 at the second, and the three valuation strata at depth 9.

For the obstruction, use Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` with the prepared compiled imports of the pinned square-dilate study. Put their object directories and the working directory on `LEAN_PATH`. Run `lean -o CompanionObstruction.olean CompanionObstruction.lean` followed by `leanchecker -v CompanionObstruction`. The [Lean replay record](lean-replay.txt) records the checked scope and exit statuses.

## Source anchors

- [First resolving count](https://github.com/nousentllc/riemann-hypothesis/blob/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates/dilates/DilateCompanion.lean)
- [Primitive permutation](https://github.com/nousentllc/riemann-hypothesis/blob/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates/dilates/DilatePrimitivePivot.lean)
- [Square predecessor and cofinal precision cells](https://github.com/nousentllc/riemann-hypothesis/blob/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates/dilates/DilateStableOddAll.lean)
- [Original transport route for the square targets](https://github.com/nousentllc/riemann-hypothesis/blob/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates/dilates/DilateTransport.lean)
- [Original regular-fiber comparison](https://github.com/nousentllc/riemann-hypothesis/blob/17263859a4d27c62cfc67571737355f61a080806/research/uriel/experiments/ramified-square-dilates/bridge/RamTransportForm.lean)
