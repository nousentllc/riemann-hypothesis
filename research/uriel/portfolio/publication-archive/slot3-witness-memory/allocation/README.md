# A 27-value record that recovers eleven positive answers

At the same storage alphabet size, the record can improve both overall answer coverage and positive recall in the slot-3 benchmark. Retaining three raw base-3 digits licenses 4,992 of the 5,184 decisions and zero of the 64 positives. The alternative below licenses 4,993 decisions and 11 positives. Eleven is the largest positive count possible at the old coverage under the stated zero-error rules. [Registered follow-up](PROTOCOL.md) · [Complete results](results.json)

The input is a bound, attested center residue for the single-center slot at cutoff 64. The record is written before the question arrives. A decoder must answer truthfully for every residue consistent with a tag or abstain. All 81 residues and 64 query weights receive equal weight. This benchmark assumes the writer has access to the particular witness. Each encoder uses 27 possible values. Shared encoding rules, witness authentication, and transmission overhead are outside the value budget. [Source labels and decoding definitions](../README.md)

| Record | Licensed positive | Licensed negative | Withheld | Total licensed |
|---|---:|---:|---:|---:|
| Three low base-3 digits | 0 | 4,992 | 192 | 4,992 |
| One empty tag, eleven individual positives, seven triples and eight groups of four | 11 | 4,982 | 191 | 4,993 |

Assign one tag to all 17 residues whose exception set is empty. Reserve one tag each for weights 1 through 11. Use seven tags for successive triples from 12 through 32, and eight tags for successive groups of four from 33 through 64. For a group of three, any of its three questions could be positive, so the decoder withholds three answers on each of its three states. The triples and groups of four give exactly 7 × 9 + 8 × 16 = 191 withheld answers. Reversing the order of all 64 weights produces the same aggregate result while protecting different named weights.

## Why eleven is optimal

A positive answer is licensed exactly when that weight's one positive state has its own tag. In any candidate assignment, collect the empty states into one of their existing tags that has the fewest distinct positive weights. This move never increases the number of withheld pairs or decreases the number of licensed positives. Each moved empty state now faces at most as many ambiguous questions. The receiving tag already contained an empty state. Each vacated tag can only become more informative. Unused labels are permitted.

If the tag containing all 17 empties also contains r positive states, it contributes r(r+17) withheld pairs. Each positive-only group of size t ≥ 2 contributes t², and a singleton contributes zero. With the numbers of pure singleton and multi-state groups fixed, the sum of these squares is minimized by making the multi-state groups differ in size by at most one. Moving one state from a larger to a smaller group proves this directly whenever their sizes differ by at least two.

The program enumerates all possible counts of singleton tags, multi-state tags and positives sharing the empty tag. It computes the minimum withheld count for every requested positive-recall target. Eleven positives require at least 191 withheld decisions. Twelve require at least 196. The raw-digit allowance is 192. As an independent check, it enumerates 2,753 partitions of labelled states on smaller populations, including assignments splitting the empties, and reproduces all 22 optimum curves. [Optimizer, decoder and controls](allocation.py)

This is an aggregate improvement. The new grouping loses 138 previously licensed negatives. It newly licenses 128 negatives and eleven positives. Picking which eleven weights receive their own tags is a design choice that would need a real query distribution or an explicit service priority. The result answers a narrow question for provenance-sensitive retrieval: among records of equal size and coverage, how effectively can we retain rare, defensible positive answers? It measures no performance of a deployed memory architecture.

## Reproduce

From this directory, run the command below with the adjoining repository checkout. The runner checks the original Git blob and the registered follow-up hash. Python 3.9.6 and 3.13.2 reproduced the same JSON.

```sh
python3 -B allocation.py --repo ../../../riemann-experiments > /tmp/slot3-allocation.json
cmp /tmp/slot3-allocation.json results.json
```
