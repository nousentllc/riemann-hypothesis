# Independent presentation and decision audit

The audit reads the circuit description and the calibration table in each frozen **user presentation**. It computes the row predicate with integer-rational arithmetic using the threshold printed in the question. For each record exactly nine lines change between views: the header and the eight candidate rows, each by appending one field. The audit also checks the original statement, state identities, switch settings, currents, initial lamp, lookup values, response format text and line endings for identity across views. Comparing each parsed entry with the frozen investigator data provides a separate check on the printed table. The 96 checked comparisons comprise 48 physical candidate rows appearing on both initial-lamp variants.

The presentation audit reconstructs every compatible state set from the initial H/L reading, partitions that set under each optional meter, and computes the strongest attainable verdict. The schedule contains exactly one session per record per view. Every actionable case has four compatible states and one decisive meter. All positions are represented twice. The maximum-balance meter rule, using uniform tie breaking and always requesting one observation, gives an expected 7/3 decisive selections in six trials on this panel. Four records have three evenly splitting meters, and two have two. These baselines characterize the constructed records.

## A check on conditioning

Encode the target as +1 for Y and −1 for N, and a meter as +1 for H and −1 for L. Sum their products over the four compatible switch settings. Every decisive meter scores +4 or −4 and every alternative scores zero here. Positive four means H licenses Y; negative four means H licenses N. In four of the six actionable cases the relationship is reversed. The generally valid condition is that every nonempty possible-reading class has a single target truth. The signed-agreement shortcut works on this deliberately balanced binary subset.

The parent study defines what the model actually receives. As a separate control, apply the same maximum-absolute-agreement rule to all eight rows, ignoring the current observation, and break ties uniformly. This rule would identify four decisive meters in expectation across six cases. In DC-T5 it certainly selects the wrong meter. The distinctions between correct restriction, accidental success and inverse lamp semantics are visible in [the row-level agreement table](agreement.json). No model output enters this calculation.

## Reproduce

Run from the study directory with Python 3 and its standard library.

```sh
python3 -B audit/check.py pre
python3 -B audit/agreement.py
python3 -B audit/selftest.py
python3 -B audit/check.py post
```

The pre-check only needs the frozen records, inputs and presentations. The post-check also requires the completed local receipts and the released score tables. It independently decodes each visible JSON answer, rebuilds and hashes the full request including the output schema and seed, matches each actual returned observation to the corresponding state, and checks the hidden-state certificates against the evidence available at that stage. Any unlicensed Y/N remains counted when a later response repairs it. A session whose verdict remains U after skipping a decisive item can have a sound certificate for the evidence on hand and still miss the registered attainable target.

The offline self-test uses a temporary copy of the frozen instrument with a simulated responder. Its 24 fictitious sessions and 36 simulated requests exercise full certificates, duplicates, truncated responses and differing meter choices. It confirms rejection of a mislabeled row even after a matching manifest hash is substituted, a reversed received reading and an inflated main-scorer tally. These simulation receipts have no role in study outcomes.

## Scored receipts

The [independent rescore](post.json) matches all 24 scheduled decisions and all 35 request hashes. Every request returned a usable JSON answer within the token cap. Each presentation acquired the decisive reading on one of six actionable records. The two successes occurred on different circuits. Four favored neither presentation and the primary two-sided conditional sign test gave p = 1. Neither view certified a final answer on an actionable record. Both passed the same single irreducibly ambiguous control. Unsupported definitive assertions numbered three on raw tables and five on labeled tables. The registered development gate failed.

On circuit-03 the labeled session selected the decisive meter M2. Its L reading leaves GL and RX. Their exact currents, −7896/14255 and −4296/21523, are both below −1/6. Both rows explicitly display N. The session answered Y and repeated the initial IDs EQ and GL. EQ had been eliminated and RX was missing. On circuit-09 the raw session obtained the decisive M7=L. Here AD and DB both license Y. The session gave Y and cited only TZ, an eliminated state. These two observed responses establish different failures after a decisive reading. They do not estimate how either presentation would fare if every record had received the decisive reading. [Labeled response](../pilot/observed/circuit-03_labeled/session.json) · [Raw response](../pilot/observed/circuit-09_raw/session.json)
