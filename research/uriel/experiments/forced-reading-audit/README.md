# Can a research agent use a decisive reading once it has one?

[Research paper](Forced_Reading.pdf) · [Single-source LuaLaTeX manuscript](Forced_Reading.tex) · [All 36 responses and decision scores](pilot/results/cases.csv) · [Preregistration](https://github.com/nousentllc/riemann-hypothesis/tree/1d2c10d165a35b57f173f6f3e0d7d777b00ee911/research/uriel/experiments/forced-reading-audit)

## Outcome

On the same six fresh circuits, the local agent certified both opposite decisive readings on 1/6 layouts when it saw all eight candidates and 5/6 when it saw only the two compatible candidates. The filtered presentation met the prespecified threshold for an independent filtering study. The rule required at least two more complete decisive families, at least two more exact ID sets on the twelve decisive records, and no reduction in certified ambiguous controls.

| Measured outcome | Full table | Filtered table |
|---|---:|---:|
| Both decisive replies fully certified | 1/6 | 5/6 |
| Certified decisive records | 3/12 | 10/12 |
| Warranted verdict on decisive records | 6/12 | 10/12 |
| Exact surviving IDs on decisive records | 3/12 | 10/12 |
| Certified ambiguous controls | 1/6 | 5/6 |
| Exact surviving IDs on ambiguous controls | 1/6 | 5/6 |
| Warranted ambiguity judgments | 2/6 | 5/6 |
| Joint successes | 4/18 | 15/18 |
| Unsupported definitive answers | 4 | 1 |
| Usable responses | 18/18 | 16/18 |
| Length-limited sessions | 0 | 0 |
| Generated tokens | 5647 | 2747 |
| Server-reported service time where available | 16.21 min | 9.25 min |

Paired family results: 4 filtered-only, 0 full-only, 1 both, 1 neither. The two-sided exact conditional sign-test value is 0.125 and the 95% conditional interval for a filtered win given discordance is 39.8%–100.0%. The six layouts are purposeful. The experiment does not estimate the frequency of this effect on other problems or models.

## What the responses show

**Where the full-table failures occurred.** Fourteen of the eighteen full-table responses named exactly two distinct settings. All fourteen verdicts agreed with the labels on the two settings actually named. Ten of those pairs included a setting inconsistent with at least one supplied reading. On circuit F6, the first lamp left GW and LB below the threshold and YW and WB above it. When M8 was low, the two survivors were YW and WB. The full-table session kept GW and WB and answered U, although GW reads high. When M8 was high, the two survivors were GW and LB. That session kept YW and LB and again answered U, although YW reads low. The filtered sessions certified yes for low and no for high, supplying both required witnesses each time. This example identifies an error observable in the outputs without inferring a private reasoning process. [Full low-reading response](pilot/observed/forced-16_full/response.json) · [Full high-reading response](pilot/observed/forced-17_full/response.json)

**Two timeouts.** Both occurred on the two decisive filtered sessions for F1. The model returned usable output in the other 34 sessions. The registered analysis counts both timeouts as failed. Across all nine combinations of their possible ID-and-certification outcomes, the net complete-layout gain ranges from four to five, the net decisive-ID gain from seven to nine, and the ambiguous-control gain stays at four. All nine meet the threshold. Client wall time for all 36 sessions spanned 35.69 minutes. Service and token counters were available on only 16 of 18 filtered calls. [Missing-response sensitivity](missing-sensitivity/results.json) · [Elapsed time and usage](audit/runtime.json)

**Next discriminating test.** On fresh layouts, keep all eight rows and mark the two eligible rows. Compare that display with both the full unmarked table and the two-row display. A marked-table gain would show that the eligibility cue can help even at full row count. Add records with the same warranted verdict and different supporting IDs, so a model that remembers a verdict must still update its witnesses.

## What was physically and experimentally controlled

Each calibration table has eight settings of three switches. One initial and one second lamp reading are given in advance. Each individual observation leaves four states with both target signs possible. Their intersection always has exactly two states. Twelve decisive records leave two equal target signs, and six controls leave opposing signs. Three of the six decisive meters have an inverse sign mapping. All 48 physical states were checked by two exact electrical calculations; 352 voltages and 632 branch currents agreed. The six network sizes differ from the fourteen previously studied and from each other. [Circuit generation and verification](circuits/README.md)

The four dozen generated physical states yield 18 logical records; each record was served once in each presentation in a fresh context. Both arms see the same instruction, exact signed currents, precomputed truth labels, observations, task, and output grammar allowing all eight IDs. The sole prompt edit deletes the six excluded rows. The exact truth labels remain visible for each displayed candidate. A mechanical filtered reader can copy both visible IDs and test whether their labels agree, certifying all 18 records. These data measure what a deterministic display operation does for an agent. Removing distractors also shortens the prompt and reduces how much state selection the model must do. [Independent controls](audit/pre.json) · [Full protocol](pilot/DESIGN.md)

## Each observed verdict and submitted set

The expected column gives the warranted verdict and both required IDs. A mixed pair warrants U. The records have no designated hidden switch setting.

| Circuit / record | Supplied lamp | Expected | Full response | Filtered response |
|---|---|---|---|---|
| DC-F1 / forced-00 | M7=L | N [LE RK] | U [FS QX] | missing [missing] |
| DC-F1 / forced-01 | M7=H | Y [PT ZD] | Y [PT] | missing [missing] |
| DC-F1 / forced-02 | M4=L | U [LE ZD] | N [QX LE] | U [ZD LE] |
| DC-F2 / forced-03 | M7=H | Y [BV DS] | Y [BV DS] | Y [BV DS] |
| DC-F2 / forced-04 | M8=H | U [DS XN] | Y [BV DS] | Y [DS] |
| DC-F2 / forced-05 | M7=L | N [IT XN] | N [XN IT] | N [XN IT] |
| DC-F3 / forced-06 | M2=L | U [DE SS] | U [DE SS] | U [DE SS] |
| DC-F3 / forced-07 | M7=L | N [DE HR] | U [DE SS] | N [DE HR] |
| DC-F3 / forced-08 | M7=H | Y [RY SS] | Y [RY UT SS] | Y [RY SS] |
| DC-F4 / forced-09 | M2=L | Y [DL NV] | Y [DL NV] | Y [DL NV] |
| DC-F4 / forced-10 | M2=H | N [AQ WM] | N [EB WM AQ] | N [WM AQ] |
| DC-F4 / forced-11 | M3=H | U [DL WM] | N [WM AQ] | U [DL WM] |
| DC-F5 / forced-12 | M2=H | N [CZ HK] | U [LQ HK] | N [HK CZ] |
| DC-F5 / forced-13 | M7=L | U [CZ TH] | U [LQ CZ] | U [TH CZ] |
| DC-F5 / forced-14 | M2=L | Y [LQ TH] | U [BN HK] | Y [LQ TH] |
| DC-F6 / forced-15 | M5=H | U [LB YW] | N [LI] | U [YW LB] |
| DC-F6 / forced-16 | M8=L | Y [WB YW] | U [GW WB] | Y [YW WB] |
| DC-F6 / forced-17 | M8=H | N [GW LB] | U [YW LB] | N [GW LB] |

## Verification and scope

The public Git registration preceded the first inference. Local commit 8ebfd8c also preserves the freeze. A version preflight stopped before any prompts were sent because the installed Ollama server had changed from 0.40.4 to 0.40.18. Both arms then used the identical pinned gpt-oss:20b model digest, low reasoning and server 0.40.18. Temperature was zero, seeds were paired within records, and all 36 calls were local. Paid API spend was $0. The software change and different tasks preclude a causal comparison with the predecessor. [Amendment](pilot/PREFLIGHT.md) · [Previous circuit study](https://github.com/nousentllc/riemann-hypothesis/tree/90729bccc20c8f941bb79494861702259bcaddbb/research/uriel/experiments/circuit-threshold-diagnostic)

The independent evaluator rebuilt the rendered prompts and each request hash, then recomputed the case and family verdicts. The scorer was also tested on 13,824 distinct verdict/ID-subset combinations and 36 duplicate certificates. The supplementary classification checks a separate question about internal consistency: did a reader correctly state what its own submitted witnesses imply, even if it selected witnesses that the observations rule out? [Independent audit](audit/post.json) · [Supplementary rule](audit/SUPPLEMENT.md) · [Submitted witness relations](audit/submitted_pairs.json)

## Reproduce locally

From the study folder, Python 3.11 or later can reproduce these checks using the standard library and the archived visible responses. No API key or local inference server is needed for this replay.

```sh
python3 -B circuits/check.py
python3 -B pilot/run.py verify
python3 -B pilot/check_certificates.py
python3 -B audit/check.py pre
python3 -B audit/selftest.py
python3 -B pilot/analyze.py
python3 -B audit/check.py post
python3 -B audit/submitted_pairs.py
python3 -B audit/runtime.py
python3 -B missing-sensitivity/bounds.py
```

The downloadable ZIP contains the editable manuscript and PDF at the first level of its study folder, the data, checksums and study history.

**Human–AI collaboration.** Justin Candler directed the research program and authorized its continuation. Uriel/Codex designed the experiment, ran and audited the local sessions, and wrote the manuscript. The measured model received only its registered messages and response schema.
