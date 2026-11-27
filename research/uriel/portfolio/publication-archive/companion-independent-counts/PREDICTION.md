# Independent Prediction Record

Recorded before running independent finite counts or inspecting the released numerical tables (`results.json`).

## Source Revisions
- Standalone local study (`output/ramified-square-dilates/`): `d9b1a208b1d0b65b1cf9be8be42d8f3909d5aff5` (per `START_HERE.md`)
- Original revision: `40e56bab026552e089d7afcfeff08d2defb9c005` (per `START_HERE.md`)

## Proposed Stable Value for the Companion
For the companion target $4^k (1 + \pi)$ in $\mathbb{Z}_2[\pi]$ ($\pi^2 = 2$, $k \ge 1$), the proposed stable normalized six-square representation density is:
$$2 - \frac{2}{256^k}$$
Specifically:
- For $k = 1$, target $4(1 + \pi)$: $2 - \frac{2}{256} = \frac{255}{128}$.
- For $k = 2$, target $16(1 + \pi)$: $2 - \frac{2}{65536} = \frac{65535}{32768}$.

## Conjectured First Permanent Depth
- **Uniformizer depth** $d$ (working in $\mathcal{O}/(\pi^d)$): $d_0 = 4k + 2$.
  - For $k = 1$: $d_0 = 6$ (with predecessor depth $d = 5$ still giving $2$).
  - For $k = 2$: $d_0 = 10$ (with predecessor depth $d = 9$ still giving $2$).
- **Coefficient depth** $m$ (working in `S m` $\cong \mathcal{O}/(2^m) = \mathcal{O}/(\pi^{2m})$, where $d = 2m$): $m_0 = 2k + 1$.
  - For $k = 1$: $m_0 = 3$.
  - For $k = 2$: $m_0 = 5$.

## Refutation Criteria
1. **Stable value refutation:** If for any $k \in \{1, 2\}$ and any tested uniformizer depth $d \ge 4k + 2$, the exact normalized ratio
   $$\frac{\#\{(x_1, \dots, x_6) \in (\mathcal{O}/(\pi^d))^6 : \sum_{i=1}^6 x_i^2 \equiv 4^k(1+\pi) \pmod{\pi^d}\}}{2^{5d}}$$
   is not equal to $2 - 2/256^k$.
2. **First permanent depth refutation:**
   - If at $d = 4k + 1$ the companion ratio already differs from $2$ (earlier split), OR
   - If at $d = 4k + 2$ the companion ratio is not $2 - 2/256^k$, OR
   - If at $d = 4k + 2$ it equals $2 - 2/256^k$ but at some $d > 4k + 2$ (including odd depths $4k+3, 4k+5$ or even depths $4k+4$) it changes away from $2 - 2/256^k$.
