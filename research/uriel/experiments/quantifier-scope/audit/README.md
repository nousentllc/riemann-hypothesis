# Independent request and score audit

This audit imports neither the experiment's runner nor its scorer. From the study root, run the following commands with Python 3. The commands operate on archived evidence.

```sh
python3 -B audit/check.py pre
python3 -B audit/selftest.py
python3 -B audit/check.py post
python3 -B audit/verify_policies.py
```

The first command checks every hash listed in the registration manifest. It reconstructs the lamp intersection of the eight physical settings and compares the signed rational target current with the threshold on each setting. It rebuilds the displayed two-row record, input schema, seeds, order and messages. The model's label response could be known only after execution. For each child, the registration therefore commits to the hash of a request with a literal field for the future response. `pre.json` contains the reconstructed per-record label and template hashes. The circuit calculation itself has a separate exact spanning-forest verifier in `circuits/check.py`.

The second command uses invented histories in a temporary directory. One checkpoint fails, one question fails before its sibling is issued, and one complete mixed label report reverses the two IDs. It then deliberately adds a space to a shared report, passes the first sibling's answer into the second sibling's history, changes a seed, narrows the answer grammar and inserts an orphaned child. The altered requests, receipts and start markers carry mutually consistent request hashes. Comparing the archived request with the independently reconstructed request still detects each change. Missing-data bounds are compared with explicit completions for all nine partial binary pairs and all four signatures.

The third command reads each real model receipt. It reconstructs both child requests using the exact visible checkpoint text and the original two-message prefix. A different space in the reported map changes its hash. Recorded request hashes use the protocol's sorted-key JSON representation. File-byte hashes in the manifest and historical receipt hashes use whole-file bytes. The audit checks each start marker, receipt and actual request together, verifies the order of timestamps against the recorded public commit date, and independently decodes each delivered answer. These are file-based checks on the archived client records. The time comparison uses the recorded Git committer and local client clocks.

`post.json` reports each receipt and each record separately. For example, a joint response can match both the physical truth and the model's reported labels, match just one, or fail both. An incomplete answer leaves only the completion possibilities consistent with any observed sibling. All fields in the official cases CSV and all sections of its summary JSON are checked. Counts for the six layouts are descriptive, and within each layout four queries share a physical network. Hidden reasoning and answer probabilities were never observable.

The fourth command compares four cohort fits for each of nine named truth-table policies. For the 256 possible deterministic two-input tables, it verifies the fit histogram via polynomial multiplication. If a hypothesis produces signature `s` on physical pattern `p`, the histogram exponent contributed by that choice is the observed count of complete pairs in cell `(p,s)`. The four input patterns contribute independently to the algebra of a fixed mapping, regardless of any statistical dependence between actual model runs. Ties are reported by enumerating each cell's maximizing signatures.

The precursor is linked, with visible source messages and original receipt hashes, in `historical_seven.json`. If the predecessor study is also available locally, the following optional check rebuilds the seven from its physical tables and archived outputs.

```sh
python3 -B audit/prior.py /path/to/label-first-verdict
```

The previous model had to give one ternary consensus verdict with witness IDs. This study elicits two binary judgments and removes the witness-writing step. Its fresh mixed pairs can show which judgments the model delivers under the new contract. They cannot identify how it interpreted a particular earlier question.

The supplementary `reference_disagreement` calculation in `post.json` asks which mistaken maps could distinguish use of the physical labels from use of the model's own transcription. Both quantified propositions depend only on the number of positive rows. Swapping positive and negative IDs preserves both truth values. Moving from one positive row to two changes only “both,” and moving from one positive row to zero changes only “at least one.” Within branches where the two references disagree, the audit counts delivered answers matching each reference and omissions. This classifies output agreement. A single match cannot identify the model's decision process.
