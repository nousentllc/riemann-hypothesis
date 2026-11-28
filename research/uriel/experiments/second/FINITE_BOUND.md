# An enclosure for the whole principal-character window

After locating the maximum numerically, we chose two rational thresholds and a rational witness to check independently. For the pinned conductor-one function on $[256,4096]$, the fixed-point calculation establishes

$$
0.1177870105 < \max_{256\le y\le4096} G(y)/\sqrt{y} < 0.1177870108.
$$

Both endpoint values are below $0.10712985$. The lower witness is $y=30025283/100000$. The enclosure depends on the elementary bounds below and the Python implementation. It is a finite result about one function on one compact interval. Lean was used separately for the conditional analytic theorem. [Integer implementation](finite_certificate.py) · [Certificate and signed residuals](results/finite_certificate.json) · [Pinned function](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean#L10-L22)

## Constants and directed arithmetic

All interval endpoints are integers divided by $2^{128}$. Each operation rounds outwards using integer division. Integer square roots enclose $\sqrt{y}$. For $1\le z\le2$ let $t=(z-1)/(z+1)$. Keeping 44 terms of $2\sum_{j\ge0}t^{2j+1}/(2j+1)$ encloses $\log z$ when augmented on the upper side by $2(1/3)^{89}/[89(1-1/9)]$. Powers of two reduce other logarithms to this range.

For Euler's constant, put $a_k=H_k-\log k$. The telescoping difference $a_k-a_{k+1}$ equals $\int_k^{k+1}(u-k)/u^2\,du$. It lies between $1/[2(k+1)^2]$ and $1/(2k^2)$. Summing these inequalities and comparing the decreasing square-reciprocal series with its integral gives

$$
\frac1{2(n+1)}\le a_n-\gamma\le\frac1{2n}+\frac1{2n^2}.
$$

We enclose $H_n$ at $n=10^6$ by summing the fixed-point floors of its terms and adding at most $n$ fixed-point units to the upper bound. This connects the computation to the harmonic-log limit used by Mathlib. [Pinned Mathlib limit](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean#L150-L154)

## Covering every point

Trial division enumerates the prime powers and their weights $\log p$. Between two consecutive knots,

$$
G(y)=A y-B-y\log y,\qquad
A=1+\gamma+\sum_{p^j\le y}\log(p)/p^j,\quad B=\sum_{p^j\le y}\log(p).
$$

The function is continuous where a new prime power enters because its ramp starts at zero. For a proposed ceiling $C$, set $D(y)=G(y)-C\sqrt y$. On each smooth piece its second derivative is $-1/y+C/(4y^{3/2})<0$ for the chosen $C$ and $y\ge256$. The tangent at the midpoint $m$ bounds the whole closed subinterval $[a,b]$ from above. Its largest possible value is bounded by the computed upper endpoint for $D(m)$ plus the interval upper bound for $|D'(m)|(b-a)/2$.

A negative upper bound certifies a leaf. Otherwise the program bisects it. All 534 smooth pieces were covered by 553 certified leaves, to maximum depth 10. A separate evaluation at the rational witness gave a positive lower bound for $G(y)-0.1177870105\sqrt y$. Substituting the false ceiling $0.11$ triggers the rejection control. The approximate maximizer was used to choose the lower witness and thresholds. The coverage calculation uses neither a floating-point stationary point nor the initial sieve's table.
