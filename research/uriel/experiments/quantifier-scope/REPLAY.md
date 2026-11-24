# Replaying the two questions

For one record, begin with its entry in `circuits/records.json`. Its `survivors` field identifies the two settings consistent with the initial lamp and supplied second lamp. In printed order compare each signed target current with the stated threshold. Equality gives N. On scope-02, for example, ER has a positive target label and PH a negative one. ER witnesses a yes to the at-least-one question; PH witnesses a no to the both question. This single pair simultaneously supports both decisions. To reproduce the calibration independently, run the circuit generator and forest verifier.

Each folder under `pilot/observed` belongs to one fresh record. Its `labels` folder contains the original keyed label request and visible reply. After a valid label map, `any` and `both` each hold a new request with the same three-message history. The siblings have identical options, answer grammar and record seed. Their final user sentences differ by the quantifier. The following are different claims to verify.

* The checkpoint reports the public labels accurately. Match IDs to signed threshold comparisons; reordering JSON keys is immaterial for this score.
* The same checkpoint text goes into both questions. Inspect the assistant message in each branch. The bytes must match the visible checkpoint text, including whitespace. Supplying corrected labels changes the experiment.
* The two answers express the truth of the two quantified propositions. Across a mixed pair the intended ordered pair is Y/N. On YY it is Y/Y, and on NN it is N/N. Keep missing outcomes distinguishable from a delivered yes or no.

After any failed checkpoint the two branch folders are absent and the planned record remains in the primary denominator. If one branch fails after a valid map, the other can still be assessed. Reconstructing an unissued request from the truth table cannot produce a model answer.

## Reproducibility

The research ZIP contains the paper, its self-contained LuaLaTeX source, the frozen protocol, all inputs, model receipts, per-case outputs, local Git bundle and checksum manifest. From the extracted study folder use the offline commands in the README. The Python verification uses the standard library. It requires neither an API key nor a model server. Recompiling the manuscript requires LuaLaTeX and the packages listed in its preamble. The original Nous PNG is embedded in the single source. The cover, abstract, contents and body have separate opening pages, and the paper includes the human–AI collaboration disclosure.

The durable preregistration predates inference. To repeat model collection independently, restore the standalone study history from the bundled repository and open a separate worktree at its initial protocol commit, before the observed folders existed. The public branch and the standalone local history have different tree roots. Use `python3 -B pilot/run.py preflight` and `python3 -B pilot/run.py collect` there. The collector calls only local Ollama at loopback port 11434. The server version is 0.40.18 and the model is gpt-oss:20b, digest 17052f91a42e97930aa6e28a6c6c06a983e6a58dbb00434885a0cf5313e376f7. The shared checkpoint seed and the sibling seed are bound to the record; each child has the same model and decoding budget. A fresh inference run can differ with runtime or hardware. Replaying archived evidence issues no new inferences.

The [public registration](https://github.com/nousentllc/riemann-hypothesis/commit/96b7664fc17d6d27a7409b49664b5c6f5eb01469) was committed at 15:26:34 Eastern on November 24, 2026. The corresponding standalone protocol commit in the ZIP's study-history.bundle is `79856d4508469b735fa27b8b7d06b8dc9232a132`.

```sh
git clone study-history.bundle scope-replay
git -C scope-replay worktree add --detach ../scope-pre-run 79856d4508469b735fa27b8b7d06b8dc9232a132
```

If you have a clone of the full research fork, supply its path to `python3 -B audit/parent_anchors.py`. This optional check reads 17 Git blobs at the pinned parent and matches the registry of 32 prior layouts and 256 prior row IDs, plus the 14 visible receipts behind the seven motivating verdicts. The [archived anchor report](audit/parent_anchors.json) lists both the Git object identifier and SHA-256 digest of each source.
