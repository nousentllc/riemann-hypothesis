# Does displaying the threshold comparison help an agent choose its next measurement?

**Nous Independent Research · 24 November 2026**

[36-page predecessor](https://github.com/nousentllc/riemann-hypothesis/tree/42b3ce4890b5c6a584af26d34bbc54f177517871/research/uriel/experiments/binary-proof-audit-transfer) · [This paper](paper/Circuit_Threshold_Diagnostic.pdf) · [Editable LuaLaTeX manuscript](paper/Circuit_Threshold_Diagnostic.tex) · [Frozen public registration](https://github.com/nousentllc/riemann-hypothesis/tree/61cfbf1743ee0bf2383199f1ab4fe3442c5bf65b/research/uriel/experiments/circuit-threshold-diagnostic)

## Finding

Displaying whether each current exceeds its threshold yielded one decisive meter choice in six, just as reading the fractions did. The successes occurred on different circuits. Neither session that obtained a decisive reading submitted a supported final answer. The preregistered threshold required a net gain of at least two decisive choices and at least one certified actionable answer. This pilot did not reach it.

| Outcome | Raw currents | Same currents with Y/N |
|---|---:|---:|
| Selected the decisive meter on actionable records | 1/6 | 1/6 |
| Selected the decisive meter and certified the final answer | 0/6 | 0/6 |
| Certified final cases across all three strata | 1/12 | 1/12 |
| Certified the initial verdict on the evidence then visible | 5/12 | 6/12 |
| Solved both records of a layout | 0/6 | 0/6 |
| Unsupported assertions over actual turns | 3 | 5 |
| Usable final decisions | 12/12 | 12/12 |
| Model calls | 17 | 18 |
| Length-limited calls | 0 | 0 |
| Generated tokens | 7741 | 6743 |
| Cumulative model service time | 9.03 min | 7.59 min |

On the primary outcome, the paired counts were 1 labeled-only, 1 raw-only, 0 both and 4 neither. The exact two-sided sign-test value was 1, with the conditional 95% interval for a labeled win given discordance 1.3% to 98.7%. The model and the six constructed topologies define the scope. The two arms had the same current values and physical evidence. The extra column changes both accessibility of the comparison and its visual prominence. This design measures the effect of displaying the bit. It cannot identify a private computation.

## Where the decisions diverged

For each record below, the meter shown in the second column is the only one whose every possible reading determines the target. The target answer is for the designated hidden setting. A certified answer includes exactly the surviving candidate IDs.

| Actionable record | Deciding meter / answer | Raw action and outcome | Labeled action and outcome |
|---|---|---|---|
| circuit-00 (DC-T1) | M7 / Y | no meter, U (no usable request) | M2, U (wrong meter) |
| circuit-03 (DC-T2) | M2 / N | no meter, U (no usable request) | M2, Y (decision or missing) |
| circuit-05 (DC-T3) | M8 / N | no meter, U (no usable request) | no meter, U (no usable request) |
| circuit-06 (DC-T4) | M6 / N | M5, Y (wrong meter) | M5, N (wrong meter) |
| circuit-09 (DC-T5) | M7 / Y | M7, Y (certificate) | M3, Y (wrong meter) |
| circuit-10 (DC-T6) | M4 / Y | M3, Y (wrong meter) | no meter, U (no usable request) |

| Control type | Raw certified | Labeled certified |
|---|---:|---:|
| Initially settled | 0/3 | 0/3 |
| Irreducibly ambiguous | 1/3 | 1/3 |

Both presentations initially answered U on all twelve records, including all three on which the initial lamp had already settled the claim. Every one of the 35 model calls returned an accepted response. Timeouts and malformed submissions account for none of the observed failures.

**What happened after each decisive reading.** In circuit-09, the raw-current session requested M7. The low reading left AD and DB, both above the signed threshold. The model answered yes but returned just TZ, a below-threshold candidate whose M7 reads high. In circuit-03, the session with displayed labels requested M2. The low reading left GL and RX, both labeled no. It returned yes and cited EQ and GL. The initial lamp had already ruled out EQ. On the sealed data these failures are observable errors of evidence use even after the needed measurement was obtained. [Raw circuit-09 receipt](pilot/observed/circuit-09_raw/session.json) · [Labeled circuit-03 receipt](pilot/observed/circuit-03_labeled/session.json)

**Next experiment.** On fresh layouts, give every session the same decisive meter reading up front. Randomize whether the agent sees all rows or only those consistent with the two observed lamps. Keep the truth column, instructions and certificate requirements fixed. This would test whether identifying the surviving candidates is a bottleneck. It would also show whether the agent can state the common sign and list all supporting IDs once the filtering has been done for it. The present pilot supplies two observed failure examples and cannot estimate how frequently each would recur under a forced reading.

[All 24 scored paths](pilot/results/cases.csv) · [Aggregates and first-failure attribution](pilot/results/summary.json) · [Independent public-prompt and response audit](audit/post.json)

## What is known about the instrument

The original checklist-versus-procedure pilot used exact physical readings, but the model had to compare a signed target current with a rational threshold itself. Here both arms use the same 125-word proof-derived instruction. We used the previous pinned local gpt-oss 20B low configuration, temperature zero, fresh contexts and matched seeds. The scored variable is the presentation alone. Every label can be checked against public numbers, and no label marks the chosen physical setting. Local inference made zero paid API calls. An independent byte comparison against predecessor commit 42b3ce4 confirmed the identical system instruction and the verbatim source of the adapter, schema, public prompt, evidence filtering and scoring functions. [Protocol and hypotheses](pilot/DESIGN.md) · [Model, seed and prompt hashes](pilot/freeze.json)

The six new networks differ in vertex/edge counts from each other and all eight historical networks. They have 48 physical switch settings. Exact nodal elimination and independent two-root forest enumeration agree on 312 voltages and 536 branch currents. Each actionable observation leaves four candidates, two on either side of the target. Exhaustive verification checks all 61 reachable record/meter/reply combinations. Fixed menu position and first most evenly splitting meter each solve two actionable records of six. A decisive meter leaves zero opposite-verdict pairs with the same reading. An evenly splitting distractor can leave the answer undecided after either reading. [Circuit definitions and checks](circuits/README.md) · [Policy controls](pilot/policy_controls.json)

After registration and before inspecting completed outcomes, we measured fixture sensitivity to four alternative signed-comparison rules. Replacing > with ≥ changes two state labels while preserving all six decisive actionable meter choices. Nearest-tenth comparisons change seven state labels and preserve only three of those six choices. Under a magnitude interpretation, one example retains exactly the same decisive meter even as its actual warranted sign reverses. These checks describe how different predicates behave on the sealed circuits. [Arithmetic controls](arithmetic-controls/README.md)

## Reproduce

From the extracted study directory, use Python 3.11 or later with the standard library. The commands below use the archived completions and require no model server or API key.

```sh
python3 -B circuits/check.py
python3 -B pilot/run.py verify
python3 -B audit/check.py pre
python3 -B pilot/analyze.py
python3 -B audit/check.py post
python3 -B arithmetic-controls/check.py
```

The ZIP also contains a checksum inventory and local Git bundle, including the registration commit d2dabb7, which preceded the first request. Public commit 61cfbf1 publishes the frozen protocol, prompts and initial audit. Compiling the paper twice with LuaLaTeX regenerates the document using its single source. The original proof archive was a source of the research question. The present model trial and circuit arithmetic are independent of a Lean kernel replay.

**Human–AI collaboration.** Justin Candler directed the research program and approved the follow-up. Uriel/Codex constructed the instrument, administered the local sessions, checked the evidence and prepared the manuscript. The model under evaluation received only the frozen session inputs.
