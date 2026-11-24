# How much could the two missing answers change?

The registered analysis counted both missing sessions as zero. Both were local transport errors in the filtered view on the two decisive records of the same layout, DC-F1. The first required N and the second required Y. All other 34 decisions were readable and are held fixed in this analysis. No ambiguous control was missing.

| Filtered minus full | Registered zero-credit value | Sharp range replacing the two missing decisions |
|---|---:|---:|
| Layouts with both decisive records certified | +4 | +4 to +5 |
| Decisive records with exact survivor IDs | +7 | +7 to +9 |
| Certified ambiguous controls | +4 | +4 |

The two substitutions cannot add two complete layouts: their shared layout is added only when both missing records receive completely certified answers. The nine ordered assignments of (wrong IDs, exact IDs with wrong sign, complete certificate) to those two records produce four joint triples. In the order of the table, those are (4,7,4), (4,8,4), (4,9,4) and (5,9,4). Every triple clears all three registered thresholds. The conclusion about the development gate is insensitive to any possible resolution of these two omissions. Its scope still depends on this model, the selected networks and the recorded answers in the other 34 sessions.

The grouped enumeration and the independent monotonic-extremes check both reproduce these bounds. The grouped method also supports the hypothetical case in which every session is missing. Equivalence-class counts carry no probability interpretation and the missing responses were never regenerated. The primary comparison, including its sign test, remains the registered zero-credit analysis.

[Pre-outcome supplemental specification](PROTOCOL.md) · [Machine-readable bounds](results.json) · [Filtered transport receipt for forced-00](../pilot/observed/forced-00_filtered/response.json) · [Filtered transport receipt for forced-01](../pilot/observed/forced-01_filtered/response.json)

To repeat the bounds calculation on the archived data and the independent synthetic checks, run these commands from the study directory:

~~~sh
python3 -B missing-sensitivity/bounds.py
python3 -B missing-sensitivity/selftest.py
~~~
