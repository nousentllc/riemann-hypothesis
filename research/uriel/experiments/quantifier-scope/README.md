# Does the model distinguish “at least one” from “both”?

On the twelve physically mixed pairs the model answered yes to “at least one” and no to “both” on **12/12**. Among mixed pairs with both labels transcribed accurately and both replies delivered, the same count was **11/11**. It answered yes to both questions on 0 mixed pairs, no to both questions on 0, and no to the first and yes to the second on 0. Of the twelve unanimous controls, 7 received both warranted answers.

The follow-up tests the output rule on these fresh pairs. It cannot determine what produced an earlier consensus verdict. Those cases used one three-way judgment and a list of witness IDs. Here each question receives an independent binary answer.

**Where the five fresh errors first appear.** On five of the six two-negative pairs the model transcribed one negative row as positive. Each resulting yes to “at least one” agreed with its own report and contradicted the printed evidence. All 48 binary answers agreed with the submitted reports. Only those five branches distinguish a decision based on the submitted map from one based on the original table. The model followed its submitted value on all five.

| Negative ID reported as positive | Two-negative record | Same row reported as negative elsewhere |
|---|---|---|
| UH | [scope-00](pilot/observed/scope-00) | [scope-03](pilot/observed/scope-03) |
| CM | [scope-04](pilot/observed/scope-04) | [scope-06](pilot/observed/scope-06) |
| DV | [scope-10](pilot/observed/scope-10) | [scope-09](pilot/observed/scope-09) |
| II | [scope-16](pilot/observed/scope-16) | [scope-19](pilot/observed/scope-19) |
| NY | [scope-20](pilot/observed/scope-20) | [scope-21](pilot/observed/scope-21) |

An additional mixed pair, [scope-18](pilot/observed/scope-18), had the positive and negative IDs swapped. Its two final judgments both matched the physical truth. In a post hoc comparison, all 24 distinct surviving rows appeared twice with identical printed data but different partners. Each of the seven miscopied label fields was transcribed accurately on its other appearance. The pair, observation and prompt context changed together, so this comparison cannot isolate which change mattered. [Paired row evidence](audit/repeated_rows.json)

[Research paper (PDF)](Quantifier_Scope.pdf) · [Single LuaLaTeX source](Quantifier_Scope.tex) · [Complete research ZIP on the branch](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-quantifier-scope/research/uriel/experiments/quantifier-scope/Nous_Quantifier_Scope_Research_Package.zip) · [Public preregistration](https://github.com/nousentllc/riemann-hypothesis/commit/96b7664fc17d6d27a7409b49664b5c6f5eb01469)

## From the seven cases to the fresh test

The preceding run produced seven positive consensus claims on eight mixed cases with accurate row labels and a delivered judgment. The two labels already contained one supporting example and one counterexample. The affirmative verdict came with only the positive ID in 5 cases and both IDs in 2. These are two distinct public failure patterns under one verdict. [Seven historical transcripts with source links and checksums](audit/historical_seven.json)

The new panel has six circuit layouts. Every layout contributes four distinct survivor pairs. Two independent calculations of the signed current supply each physical label. The public table includes the labels, so this task measures using the table rather than solving the electrical equations. A first call asks for the two surviving labels by ID. Separate follow-up calls receive the identical full prompt and verbatim report. The only difference between sibling messages is the quantifier in the final sentence. Either child can be asked first. Both orders occur within each pattern. [Frozen protocol](PROTOCOL.md) · [How to replay a case](REPLAY.md)

## What the model returned

It transcribed both labels accurately on 18/24 records (41/48 individual fields). The at-least-one branch delivered 24/24 and matched the electrical truth on 19/24. The both branch delivered 24/24 and matched on 24/24. Jointly warranted pairs across the entire panel numbered 19/24. All planned records enter these denominators.

Input letters give the two physical labels in printed order. Output letters always give answers in the order (at least one, both). Each row contains six cases.

| Physical pair | Both answers warranted | Output Y,Y | Output Y,N | Output N,Y | Output N,N | Incomplete |
|---|---:|---:|---:|---:|---:|---:|
| YY | 6/6 | 6 | 0 | 0 | 0 | 0 |
| NN | 1/6 | 0 | 5 | 0 | 1 | 0 |
| YN | 6/6 | 0 | 6 | 0 | 0 | 0 |
| NY | 6/6 | 0 | 6 | 0 | 0 | 0 |

| Actual answers on mixed pairs | Individual records |
|---|---|
| Yes to at least one, no to both | [scope-18](pilot/observed/scope-18), [scope-19](pilot/observed/scope-19), [scope-21](pilot/observed/scope-21), [scope-05](pilot/observed/scope-05), [scope-09](pilot/observed/scope-09), [scope-02](pilot/observed/scope-02), [scope-22](pilot/observed/scope-22), [scope-15](pilot/observed/scope-15), [scope-12](pilot/observed/scope-12), [scope-08](pilot/observed/scope-08), [scope-03](pilot/observed/scope-03), [scope-06](pilot/observed/scope-06) |
| Yes to both questions | none |
| No to both questions | none |
| No to at least one, yes to both | none |
| Missing at least one answer | none |

Allowing every unobserved binary answer to take either value gives a mixed separation count from 12 to 12 out of twelve. Because siblings share a checkpoint and pairs share layouts, the single-branch answers do not provide 48 independent measurements of a general model capability. [Full score](pilot/results/summary.json) · [Case ledger](pilot/results/cases.csv)

## Which alternatives fit?

On a nonempty pair, two yeses to the questions imply all-positive, yes/no implies mixed, and two noes imply all-negative. No/yes violates the implication from “both” to “at least one.” A universal yes on a mixed pair makes the same public claim as the earlier positive consensus verdict, even when the negative row has already been named.

One positive row is a witness to “at least one.” One negative row is a counterexample to “both.” For a mixed pair, using OR twice predicts two yeses. Using AND twice predicts two noes. A rule that always answers yes to the first wording and no to the second can pass every mixed pair and fails every unanimous control. The two mixed orders also distinguish copying the first or the second row. The table reports exact paired matches. [Finite rule catalogue and sensitivity calculation](theory/README.md)

| Candidate rule | All 24 | Mixed 12 | Accurate, completed mixed pairs |
|---|---:|---:|---:|
| Evaluate each quantifier as written | 19/24 | 12/12 | 11/11 |
| Answer both with at least one | 7/24 | 0/12 | 0/11 |
| Answer both with both | 7/24 | 0/12 | 0/11 |
| Reverse the questions | 7/24 | 0/12 | 0/11 |
| Always yes | 6/24 | 0/12 | 0/11 |
| Always no | 1/24 | 0/12 | 0/11 |
| Always Y then N | 17/24 | 12/12 | 11/11 |
| Copy first row twice | 7/24 | 0/12 | 0/11 |
| Copy second row twice | 7/24 | 0/12 | 0/11 |

The best fit over all 256 deterministic tables using only the two ordered true labels is 23/24 paired outputs. This is an in-sample descriptive ceiling. Different implementations can have the same input/output table. The test identifies differences in behavior available at this interface. [All candidate scores](theory/policy_scores.json)

## Replay and provenance

The run used local gpt-oss:20b with low reasoning, Ollama 0.40.18, and no paid API calls. The maximum was 72 calls. The actual run issued 72 (24 labels, 24 at least one, 24 both). The registered order, digest, decoding settings and canonical hashes are archived. [Freeze manifest](pilot/freeze.json) · [Order](pilot/order.json) · [Actual requests and visible replies](pilot/observed) · [Independent audit](audit/post.json)

From the extracted quantifier-scope folder, the following commands reproduce the calibration, score and independent audit using standard-library Python. The inference service is unnecessary for this replay.

~~~sh
shasum -a 256 -c SHA256SUMS
python3 -B circuits/select_panel.py
python3 -B circuits/cases.py
python3 -B circuits/check.py
python3 -B pilot/run.py verify
python3 -B pilot/selftest.py
python3 -B pilot/analyze.py
python3 -B audit/check.py pre
python3 -B audit/selftest.py
python3 -B audit/check.py post
python3 -B theory/logic.py design
python3 -B theory/logic.py results
python3 -B audit/verify_policies.py
python3 -B audit/repeated_rows.py
~~~

The ZIP contains the PDF and its single TeX source in the same folder as this README. To compile the paper, run LuaLaTeX three times in a temporary directory containing only the .tex file. The source contains the Nous PNG bytes. The ZIP also includes the local standalone research history, including its pre-inference commit, and SHA-256 checksums. The public branch is additive on the prior experimental branch. This is a behavioral experiment motivated by witness handling in a proof study. It adds no Lean declaration or kernel check.
