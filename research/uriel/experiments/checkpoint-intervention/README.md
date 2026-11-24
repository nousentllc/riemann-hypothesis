# When a report changes the verdict

A one-letter repair removed the false existential claim in all five historical cases. With the previous mistaken report, five fresh replays returned yes. With the same circuit table and a one-character repair, five newly issued calls returned no. On each of those records the answer to “both” remained no.

[Research paper](Checkpoint_Intervention.pdf) · [Single LuaLaTeX source](Checkpoint_Intervention.tex) · [ZIP on GitHub](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-checkpoint-intervention/research/uriel/experiments/checkpoint-intervention/Nous_Checkpoint_Intervention_Package.zip) · [Public preregistration](https://github.com/nousentllc/riemann-hypothesis/commit/ff14cfe41400155704437d25fd63d884208cf3ab)

## The decisive comparisons

Each entry is the new answer with the faithful report followed by the new answer with the conflicting report. Every physical table stayed fixed within each comparison. There were six layouts and twelve records.

| Circuit truth | Question | Observed faithful → conflicting | Records |
|---|---|---|---:|
| Two negative rows | At least one positive? | No → Yes | 6/6 |
| Two negative rows | Both positive? | No → No | 6/6 |
| Two positive rows | At least one positive? | Yes → Yes | 6/6 |
| Two positive rows | Both positive? | Yes → No | 6/6 |

The historical five are a subset of the first group. They are scope-00 (UH), scope-04 (CM), scope-10 (DV), scope-16 (II), and scope-20 (row ID NY). On scope-14 the original negative map was faithful. Introducing a false Y on PY elicited a new false existential yes. The six positive records test the opposite direction by introducing a false negative. Evidence and checkpoint made incompatible predictions on exactly twelve conflict-arm questions. The model gave the checkpoint-implied answer on all twelve. All 24 faithful-arm answers matched the circuit. The other twelve conflict-arm questions remained physically warranted.

The same public report can help diagnose a failure and then carry that failure into a downstream judgment. The intervention establishes sensitivity to supplied conversation history under the recorded conditions. A report-following policy fits every response, as could other policies that behave identically on this restricted domain. The experiment does not establish which internal process produced the behavior. The five selected binary cases differ from the seven earlier ternary consensus cases. No new Lean theorem or kernel build is part of this study.

## Example you can check

In scope-00 the exact target currents on UH and PH are −4638141/31551037 and −32067864/198392179 amperes. Both are below −1/8. With the faithful report {"UH":"N","PH":"N"}, the model returned N to existence. With {"UH":"Y","PH":"N"}, it returned Y. Both versions returned N to universality. The same physical and user messages appear in every appropriate comparison. [Four actual calls](observed/scope-00) · [Full case ledger](cases.csv)

## Evidence and replay

The [previous study](https://github.com/nousentllc/riemann-hypothesis/tree/4288df5b22461eee3ad77a15802f80b53a6be527/research/uriel/experiments/quantifier-scope) supplied the 12 homogeneous records. The present release deliberately reuses these circuits to make within-record interventions. The original respondent and decoding settings were preserved. All 48 new outputs were usable, and the 24 untouched request replays reproduced all 24 original binary answers. All calls ran locally at zero direct API cost. The 24 additional requests varied a single character of the historical assistant-role message. [Frozen protocol](PROTOCOL.md) · [Hashed schedule](freeze.json) · [Parent source manifest](sources.json) · [Independent audit](audit.json)

From the extracted study directory, offline verification needs Python 3.9+ and no other Python packages.

~~~sh
shasum -a 256 -c SHA256SUMS
python3 -B study.py verify
python3 -B physics.py
python3 -B study.py score
python3 -B audit.py
~~~

The optional argument to the last command is --repo followed by the path to a local clone of the research fork. It checks 61 parent Git blobs, including the full parent registry and the original request/response extracts. The electrical verifier starts from each actual user prompt and solves the nodal equations over rational numbers. It recomputes both lamps and the signed current for all eight possible switch settings per record. [Reconstructed circuit states](physics.json)

To replicate inference, clone study-history.bundle into a fresh directory and check out its initial commit c51e123071a56b7a6835c73c9dbaafad0d5554a1. From that directory run python3 -B study.py collect followed by python3 -B study.py score. Collection needs the pinned gpt-oss:20b model and Ollama 0.40.18 at 127.0.0.1:11434. The frozen schedule includes the seeds, request hashes and arm order. A repeat on different hardware or software may yield different outputs. The archived runner journals dispatch and resumes without resending a recorded call.

The ZIP includes the paper and its single LuaLaTeX file side by side, the study history, visible responses and checksums. For a deterministic PDF build under the release's LuaHBTeX 1.24.0, set SOURCE_DATE_EPOCH=1795551886 and FORCE_SOURCE_DATE=1 and compile the single TeX file three times. The original Nous PNG is embedded.
