# Before the verdict

[Research paper](Label_First.pdf) · [Single LuaLaTeX source](Label_First.tex) · [Complete research ZIP](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-label-first-verdict/research/uriel/experiments/label-first-verdict/Nous_Label_First_Research_Package.zip) · [All scored decisions](pilot/results/cases.csv) · [Preregistration](https://github.com/nousentllc/riemann-hypothesis/tree/fba1c3a576af959ea195cd849a2245fdd3532cd4/research/uriel/experiments/label-first-verdict)

How often does the final verdict contradict two labels the model has just given accurately? On this fresh panel, 7 of 18 delivered verdicts after an accurate checkpoint did so. Direct answering produced 15/24 warranted verdicts. Labeling before deciding produced 11/24. Both conditions saw the same two surviving rows, already labeled on the page. The extra call supplied no truth feedback.

| Outcome | Direct | Labels first |
|---|---:|---:|
| Usable final answers | 22 | 23 |
| Warranted final verdicts | 15 | 11 |
| Wrong delivered verdicts | 7 | 12 |
| Undelivered final verdicts | 2 | 1 |
| Verdict and both IDs jointly accurate | 14 | 11 |

The complete matched comparison gave 5 successes shared by both workflows, 10 direct-only, 6 label-first-only and 3 neither. The label-first minus direct difference was -4 out of 24. The six-layout sign-flip reference gave p = 1/4. The interval over binary completions of all missing final responses is [-6, -3]. The six deliberately selected layouts do not constitute a random sample of future tasks.

Both keyed labels were accurate on 18/24 workflows. Label-first emitted reports on 23/24, with 41 accurate individual labels out of 48 required. A deterministic unanimity rule applied offline to the actual reports would have delivered 18/24 warranted verdicts. The comparison grants the label-first workflow an extra generation and additional context. It cannot isolate the benefit of stating labels from the benefit of another call.

## Where the verdict changed

On the 12 unanimous pairs, direct answering gave five warranted verdicts and label-first gave ten. On the 12 mixed pairs, direct gave ten and label-first gave one. The six label-first-only successes comprised five formerly unwarranted direct replies and one undelivered direct reply. Of the ten direct-only successes, nine paired with unwarranted staged verdicts and one with a missing checkpoint.

Among the 18 accurate checkpoints, every unanimous pair was judged accurately (10/10). Seven of the eight mixed pairs were called yes. On record 02 the checkpoint explicitly wrote FV=Y and RM=N. The verdict call returned Y and cited both FV and RM. Record 21 also cited both opposite witnesses while asserting Y. In the other five such errors, the final certificate retained only the positive witness. The one-of-each sign pattern was visible in both row orders.

The supplementary deterministic reducer gave 18/24 warranted verdicts from the model's submitted labels. It recovered seven failures of the second model call. All five inaccurate checkpoints had a single wrong label. None of those was repaired in the actual final verdict. These comparisons locate a loss after accurately reporting the evidence. They cannot reveal the model's private reasoning.

## Direct evidence

The three historical motivating errors included one mixed pair called yes and two positive pairs called undetermined. Their source references, SHA-256 hashes and visible answers are preserved in [the historical trace](audit/prior_errors.json). All six new circuits have graph footprints distinct from the previous 26; all 48 new switch IDs differ from the preceding 208. For each circuit both arms faced one YY, NN, YN and NY record.

| Record | Circuit | True labels (IDs in display order) | Direct verdict [IDs] | Committed labels | Final verdict [IDs] |
|---|---|---|---|---|---|
| label-00 | DC-J1 | EO=N RM=N | U [EO RM] | EO=Y RM=N | Y [EO] |
| label-01 | DC-J1 | FV=Y KS=Y | Y [FV KS] | FV=Y KS=Y | Y [FV KS] |
| label-02 | DC-J1 | FV=Y RM=N | U [FV RM] | FV=Y RM=N | Y [FV RM] |
| label-03 | DC-J1 | EO=N KS=Y | U [EO KS] | EO=N KS=Y | Y [KS] |
| label-04 | DC-J2 | BR=N WK=N | U [BR WK] | BR=N WK=N | N [BR WK] |
| label-05 | DC-J2 | BR=N NN=Y | U [BR NN] | BR=N NN=N | N [NN] |
| label-06 | DC-J2 | BF=Y WK=N | U [BF WK] | undelivered | undelivered |
| label-07 | DC-J2 | BF=Y NN=Y | U [BF NN] | BF=Y NN=Y | Y [BF NN] |
| label-08 | DC-J3 | NR=N IO=Y | U [NR IO] | NR=N IO=Y | Y [IO] |
| label-09 | DC-J3 | TX=Y PA=N | U [TX PA] | TX=Y PA=N | U [TX PA] |
| label-10 | DC-J3 | NR=N PA=N | N [NR PA] | NR=N PA=N | N [NR PA] |
| label-11 | DC-J3 | TX=Y IO=Y | Y [TX IO] | TX=Y IO=Y | Y [TX IO] |
| label-12 | DC-J4 | BL=N DT=Y | U [BL DT] | BL=N DT=Y | Y [DT] |
| label-13 | DC-J4 | SQ=Y DT=Y | U [SQ DT] | SQ=Y DT=Y | Y [SQ DT] |
| label-14 | DC-J4 | BL=N HP=N | N [BL HP] | BL=Y HP=N | Y [BL] |
| label-15 | DC-J4 | SQ=Y HP=N | N [SQ] | SQ=Y HP=N | Y [SQ] |
| label-16 | DC-J5 | ZU=N KV=N | undelivered | ZU=N KV=N | N [ZU KV] |
| label-17 | DC-J5 | QD=Y AF=Y | Y [QD AF] | QD=Y AF=Y | Y [QD AF] |
| label-18 | DC-J5 | QD=Y KV=N | U [QD KV] | QD=N KV=N | N [QD KV] |
| label-19 | DC-J5 | ZU=N AF=Y | undelivered | ZU=N AF=Y | Y [AF] |
| label-20 | DC-J6 | LM=N EM=N | U [LM EM] | LM=N EM=N | N [LM EM] |
| label-21 | DC-J6 | FM=Y EM=N | U [EW EW] | FM=Y EM=N | Y [FM EM] |
| label-22 | DC-J6 | LM=N OL=Y | U [LM OL] | LM=N OL=N | N [LM OL] |
| label-23 | DC-J6 | FM=Y OL=Y | U [FM OL] | FM=Y OL=Y | Y [FM OL] |

## Reproduce and inspect

The ZIP includes the single-file paper and PDF at the top of its study folder, full datasets, protocol, saved request/response pairs, checksums and a portable Git history. For an isolated test of the verifier and its rejection of modified message history, run `python3 -B audit/selftest.py`. The six networks were calibrated by exact nodal elimination and independently by enumeration of two-root forests. A Python standard-library replay requires no model, network connection or API key.

~~~sh
python3 -B circuits/select_panel.py
python3 -B circuits/cases.py
python3 -B circuits/check.py
python3 -B pilot/run.py verify
python3 -B pilot/analyze.py
python3 -B audit/check.py
python3 -B audit/composition.py --verify
~~~

The local server used Ollama 0.40.18, pinned gpt-oss:20b, low reasoning, temperature zero, 8,192 context and 2,048 generation tokens per call. 71 calls were issued across 48 workflows. Paid API spend was $0. A checkpoint without a usable label map gated off the corresponding verdict; final decisions were never retried. [Protocol](PROTOCOL.md) · [Reproduction instructions](REPRODUCIBILITY.md) · [Independent request and outcome audit](audit/post.json) · [Offline reduction](audit/composition.json)

**Human–AI collaboration.** Justin Candler directed the experiment. Uriel/Codex designed and ran the fresh panel, scored and checked the responses and prepared the paper. This circuit study evaluates a model’s use of supplied evidence. It adds no Lean kernel check or new claim about RH.
