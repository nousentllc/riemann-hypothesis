# How much can the meter choice reveal about arithmetic?

A reader can request the same meter as an exact reasoner while answering a different mathematical question. We tested that possibility on the frozen circuit data by recomputing all admissible cases under four specified changes to the current comparison. The control was registered locally after the model experiment's protocol and before its outcomes were examined. The model inputs, physical currents, comparator lamp tables, initial readings and returned evidence remained those of the original experiment. This is an analysis of what the instrument can distinguish.

| Assumed claim on each candidate | Changed truth labels out of 48 | Same guaranteed meter out of six | Became settled initially | Guaranteed meter lost, contingent reply still possible | Original control certificates lost out of 15 |
|---|---:|---:|---:|---:|---:|
| Registered strict signed current I > t | 0 | 6 | 0 | 0 | 0 |
| I ≥ t | 2 | 6 | 0 | 0 | 4 |
| Absolute current compared to signed threshold, abs(I) > t | 8 | 4 | 2 | 0 | 5 |
| Magnitudes on both sides, abs(I) > abs(t) | 15 | 5 | 0 | 1 | 4 |
| Nearest-tenth rounding on each operand, strict comparison | 7 | 3 | 1 | 2 | 6 |

The numerator in the first numerical column counts distinct physical settings across six topologies. Each topology's two records share eight settings. The action columns use the six records that require a guaranteed meter in the registered comparison. No alternative produces a new, different meter guaranteed to decide both ways. However, a target change may remove the need for a lookup or permit resolution only if a specific observation occurs. The last column counts verdict-and-ID certificates on the initially visible evidence for the three settled and three irreducible control records. Each settled record has one complete certificate. Each of the three ambiguous records has four unordered pairs of opposing candidates.

## What disappears in the controls

| Alternative | Controls losing at least one initial certificate | Controls losing every initial certificate | Controls whose strongest attainable verdict changes on the actual reading |
|---|---|---|---|
| Inclusive | 07, 11 | None | 07 |
| Absolute current, signed threshold | 02, 04 | 02, 04 | 02, 04 |
| Magnitudes on both sides | 02, 04, 08 | 04, 08 | 02, 04, 08 |
| Rounded tenths | 07, 11 | 07 | 07 |

Numbers give the suffix in IDs such as circuit-07. Losing some initial witnesses can coexist with a surviving demonstration of ambiguity. Likewise, a query can settle an altered claim on its actual reply even if the initial record still admits opposing witnesses and no meter will settle every possible reply.

For circuit-09, all four initial candidate currents are negative and the signed threshold is −1/4 A. For negative I, the registered predicate I > −1/4 is equivalent to |I| < 1/4. There are no equality cases among these four. Replacing the predicate with |I| > 1/4 therefore complements every answer and leaves the partition of candidates by truth intact. The same meter M7 still isolates the two truth classes for both readings. The strongest registered conclusion is yes and the strongest altered conclusion is no. Selecting M7 alone is logically incapable of distinguishing these two rules on this input.

The strict versus inclusive comparison gives a second limit. The two physical settings exactly on the threshold belong to control records 07 and 11, so all six actionable records give exactly the same optimal meter choices. A sampled session could appear to handle strict inequalities on every acquisition while missing both boundary cases. The control certificates retain sensitivity unavailable in that action count. None of these comparisons diagnoses a mental strategy in a model that issued a particular verdict. A specific unsupported comparison needs evidence in its own public output or a further controlled intervention.

The [design note](PROTOCOL.md) specifies the rules and endpoints. The [full results](results.json) give every feasible reply, outcome, changed physical label, lost and retained initial certificate, and designated actual verdict. To reproduce using Python's standard library from this directory, run `python3 -B check.py`.
