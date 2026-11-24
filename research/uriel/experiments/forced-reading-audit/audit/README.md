# Independent audit of the forced measurements

The audit reconstructs the licensed conclusion from the full **rendered public** table. It parses the exact rational currents, the threshold, both supplied lamp readings and the printed settings. It tests each truth label against the strict inequality, intersects the two evidence conditions and deletes only the six incompatible lines while preserving byte content and position on every other line. The result must equal the actual two-row prompt. Label polarity, wave assignments, target sign, family pairing and the frozen inputs are checked separately.

Every conjunction leaves exactly two IDs. For the homogeneous cells a valid certificate requires both survivors. For the mixed controls both are again necessary as the only pair with opposite labels. Thus, for this panel, full certification factors exactly into recovering the two-member set and choosing its warranted sign. Either component can fail alone. There are six layout-level trial units; the two decisive replies in each are complementary and should be scored together for the primary comparison.

## What a mechanical display policy can do

A system which simply copies both displayed IDs and reads unanimity in the filtered display certifies every record. It needs no calculation of current, independent filtering or physics knowledge on that view. Copying the two displayed IDs and reporting the sign of the first row also certifies all twelve decisive cases but fails every mixed control, despite naming both IDs. In the full display, using only one observed lamp leaves four states; either lamp alone admits both signs on every provided record. The direct solution is the same inexpensive two-predicate intersection for every full record. First-two-row and other deliberately simple deterministic baselines are enumerated in [the pre-run audit](pre.json). These policies characterize the task and cannot attribute an observed model response to a specific private computation.

There is a useful family-level limit on shortcuts. The two decisive records for the same layout use the same full table, target and initial reading. Changing the forced lamp from H to L exchanges one two-member answer set for the disjoint complement and reverses the warranted verdict. A deterministic policy indifferent to that reading in the full view can certify at most one twin and cannot complete a family. In the filtered view, copying the displayed rows can certify both even if the reader ignores the prose describing the observations. The two twin records receive different generation seeds; individual model differences between them cannot be attributed solely to the change of lamp. The matched seeds apply to the two renderings of each single record.

## Reconstructing the score

The post-run audit decodes each visible JSON completion and independently reconstructs the requested two-message conversation, pinned model configuration, paired seed and structure of the response grammar. The grammar enumerates the **same eight IDs in the same order** for the two presentations. Any absent IDs named by a filtered response can therefore be detected instead of being disallowed by a smaller grammar. The audit rechecks every request hash, every cited ID, every omission, the case endpoints and the paired decision with a separate enumeration of sign assignments. Its conditional interval comes from a second implementation using rational binomial tails, including the case of no discordant families. The occurrence counts assign every distinct excluded ID in a response to the initial-only, forced-only or neither-lamp group. Duplicate uses of one excluded ID in a single answer count as one excluded ID and a separate duplicate defect.

From the study directory run:

```sh
python3 -B audit/check.py pre
python3 -B audit/selftest.py
python3 -B audit/check.py post
```

The self-test uses fabricated completions on a temporary copy with the local inference transport replaced by a pure stub. It exercises the production request builder and scorer, then tests whether flipped table order, a response grammar narrowed to the two displayed IDs, and inflated paired results are detected. The ordinary pre-audit reads only the sealed inputs. Post-auditing requires the complete released score table and all 36 receipts.

## Completed audit

The independent checker matched every one of the 36 scheduled request hashes and reconstructed the two exact output components on all 36 records, including two filtered requests which timed out at the client and had no delivered answer. Those requests were both decisive records of DC-F1. Usage counters cover returned responses. The totals cannot establish how much server-side generation, if any, continued after the client stopped waiting.

| Endpoint | Full display | Filtered display |
|---|---:|---:|
| Both decisive records certified in a family | 1/6 | 5/6 |
| Exact IDs on decisive records | 3/12 | 10/12 |
| Warranted signs on decisive records | 6/12 | 10/12 |
| Both components on ambiguous controls | 1/6 | 5/6 |
| Interpretable delivered completions | 18/18 | 16/18 |
| Responses naming at least one excluded ID | 13/18 | 0/18 |

Four discordant families favored the filtered display, zero favored the full display, one passed with both and one failed with both. Enumerating the 16 sign allocations on the four discordances gives a two-sided probability of 1/8. The conditional 95% interval for the direction of a discordance was 0.398 to 1. The frozen development rule passed. All errors remain in the specified denominators.

An exact paired example comes from DC-F6. The initial L reading retained GW and LB, both labeled N, and YW and WB, both labeled Y. In the low-M8 record, YW/WB remained. The full response asserted ambiguity with GW and WB. Those two signs really do oppose, but GW has M8 high. In the high-M8 twin, GW/LB remained. This time the full response asserted ambiguity with YW and LB; YW has M8 low. In each case a valid rule for witnessing ambiguity was applied to a pair that included an impossible setting. Both filtered responses gave the warranted common sign and both surviving IDs. [Low-M8 full response](../pilot/observed/forced-16_full/response.json) · [High-M8 full response](../pilot/observed/forced-17_full/response.json) · [Low-M8 filtered response](../pilot/observed/forced-16_filtered/response.json) · [High-M8 filtered response](../pilot/observed/forced-17_filtered/response.json)

Among full-display responses, 15 submitted ID occurrences contradicted the joint evidence. Eight met only the initial reading, five met only the forced meter reading and two met neither. The same identifier is counted once per response. No delivered filtered response named an excluded ID. The lone delivered but uncertified filtered answer claimed Y in mixed record forced-04, submitting only DS and omitting the surviving opposite witness XN. This finite panel localizes identifiable mistakes in the answers. It does not distinguish a particular internal filtering algorithm from the shorter display and its mechanically sufficient copying strategy. [Independent per-record scores](post.json)
