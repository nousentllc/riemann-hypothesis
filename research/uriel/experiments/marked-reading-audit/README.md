# Does marking eligible switch settings work as well as showing only those settings?

[Paper](Marked_Reading.pdf) · [Single-file LuaLaTeX source](Marked_Reading.tex) · [Case scores](pilot/results/cases.csv) · [Full results](pilot/results/summary.json) · [Public preregistration](https://github.com/nousentllc/riemann-hypothesis/tree/f974856a9360819fd42233e69c1abdefbd41b816/research/uriel/experiments/marked-reading-audit)

## Result

The same local reader saw each of 24 records with all eight rows unmarked, all eight with the two survivors marked, or just the two survivors visible. A response needed the warranted verdict and exactly the two supporting IDs. The primary comparison required passing both decisive records on a layout. Marking achieved 3/6 and filtering achieved 3/6. All eight unmarked achieved 0/6.

| Measured outcome | All eight | All eight, two marked | Two survivors only |
|---|---:|---:|---:|
| Both decisive replies certified | 0/6 | 3/6 | 3/6 |
| Both mixed replies certified | 1/6 | 3/6 | 5/6 |
| All four replies certified | 0/6 | 2/6 | 2/6 |
| Certified decisive records | 1/12 | 8/12 | 9/12 |
| Certified mixed records | 5/12 | 8/12 | 11/12 |
| Certified records overall | 6/24 | 16/24 | 20/24 |
| Exact supporting ID set | 6/24 | 17/24 | 23/24 |
| Warranted verdict | 10/24 | 18/24 | 20/24 |
| Unsupported definitive claims on mixed records | 6/12 | 3/12 | 1/12 |
| Usable responses | 24/24 | 24/24 | 23/24 |

Of six layouts, 2 passed both marked and filtered presentations, 1 passed only with marks, 1 passed only with removal, and 2 passed neither. The signed marked-minus-filtered difference in complete layouts is +0/6. The exact two-sided paired sign-test probability is 1. The interval for the direction of a discordance is [0.013, 0.987]. On these six constructed circuits, a small difference or a tie cannot establish population equivalence.

Across all individual records, 14 passed in both M and F, 2 only in M, 6 only in F, and 2 in neither. Marked-only successes: marked-11, marked-23. Filtered-only successes: marked-14, marked-15, marked-16, marked-20, marked-21, marked-22. The cases are nested within circuits.

## Where marking helped and where it fell short

Marking gained ten complete answers over the unmarked table. The reader cited at least one setting ruled out by the lamps in 17 unmarked answers and six marked answers. Among the 23 filtered answers that produced text, all 23 named the exact surviving pair. Three still drew an unwarranted conclusion from that pair. The remaining filtered call, G4 record 13, used all 2,048 permitted generation tokens with no visible answer, and counted as a failure. Marking returned an answer on every call.

The case-level crossovers have specific explanations. On G5 record 16 the two stars marked JH and LX, both supporting N. The marked reply gave N but named NJ and LX, citing a row the readings excluded. The filtered reply gave N with JH and LX. Conversely, on G3 record 11 both presentations named BQ and WP, both labeled Y. The marked reply concluded Y. The filtered reply concluded U. The other marked-only win had the same pattern with two different IDs. On mixed records the model also made definite claims contradicted by a witness it had itself named. The full [excluded-ID audit](audit/excluded.json) gives each counterexample and ID.

Across all 24 matched records, two truthful stars recovered 10 of the 14 additional certifications gained by filtering over unmarked, calculated from the arm totals. That fraction is an aggregate description. It does not mean one presentation's successes contained the other's. All 72 sessions used the same fixed model, and the tables supplied the threshold label for each setting. These results describe a tested interface for reading evidence.

## Why the mixed pairs matter

On G1, M19 low leaves DA and SY. M19 high leaves KF and BU. Both pairs contain one setting above and one at or below the threshold. Both replies therefore require U, even though the high reply rules out every supporting ID from the low reply. Checking the IDs distinguishes retaining the conclusion from retaining invalid reasons. Each layout has an analogous pair. On the decisive meter the warranted conclusion also changes when the observed reading changes.

## What each display supplied

Unmarked and marked tables have identical lengths in characters. In the marked tables exactly two dots become stars. In the filtered tables exactly six rows disappear, while the two surviving rows retain their neutral dots. All three versions give both readings, the same marker legend and an output grammar admitting all eight IDs. Reading the marked or displayed pair and testing whether both target labels agree is a deterministic perfect policy. Removing the other six also shortens the text. The contrasts measure the behavior of one fixed reader on these displays.

One initial lamp or one second lamp on its own leaves four settings and both target truth values in all 24 records. Combining them leaves exactly two. The independent forest and nodal solvers agree on 384 exact node voltages and 640 branch currents across all 48 physical switch configurations. The six new graph footprints exclude all 20 older layouts. [Circuit specifications and exact checks](circuits/README.md)

## All 24 matched decisions

Y and N mean every compatible setting agrees. U means the two compatible settings disagree. Brackets contain the ID list returned by the model in its original order. Omitted answers count as failures.

| Circuit and record | Reading | Expected | Unmarked | Marked | Filtered |
|---|---|---|---|---|---|
| DC-G1 / marked-00 | M11=L | N [DA KF] | N [PN DA KF GF KM GE SY BU] | N [DA KF] | N [DA KF] |
| DC-G1 / marked-01 | M11=H | Y [BU SY] | U [KF SY] | Y [SY BU] | Y [SY BU] |
| DC-G1 / marked-02 | M19=L | U [DA SY] | U [SY DA] | U [DA SY] | U [DA SY] |
| DC-G1 / marked-03 | M19=H | U [BU KF] | Y [SY BU] | U [KF BU] | U [KF BU] |
| DC-G2 / marked-04 | M16=H | N [TR YS] | N [TR] | N [TR YS] | N [TR YS] |
| DC-G2 / marked-05 | M22=L | U [VD YS] | N [TA] | Y [VD] | Y [YS VD] |
| DC-G2 / marked-06 | M22=H | U [AA TR] | N [TR YS] | U [AA TR] | U [AA TR] |
| DC-G2 / marked-07 | M16=L | Y [AA VD] | N [TA] | Y [AA VD] | Y [AA VD] |
| DC-G3 / marked-08 | M21=L | U [BQ KD] | U [BQ FA] | U [BQ KD] | U [BQ KD] |
| DC-G3 / marked-09 | M21=H | U [FA WP] | U [FA WP] | U [FA WP] | U [FA WP] |
| DC-G3 / marked-10 | M22=L | N [FA KD] | U [BQ KD] | N [FA KD] | N [FA KD] |
| DC-G3 / marked-11 | M22=H | Y [BQ WP] | U [FA WP] | Y [BQ WP] | U [BQ WP] |
| DC-G4 / marked-12 | M17=H | U [DY VP] | U [DY VP] | U [DY VP] | U [DY VP] |
| DC-G4 / marked-13 | M22=L | Y [DX VP] | Y [NA DX] | U [NA DX] | Missing (invalid) |
| DC-G4 / marked-14 | M22=H | N [DY NA] | U [DY VP] | U [DY VP] | N [DY NA] |
| DC-G4 / marked-15 | M17=L | U [DX NA] | U [NA DX] | N [NA DX] | U [DX NA] |
| DC-G5 / marked-16 | M13=L | N [JH LX] | Y [CH NS ZS SU] | N [NJ LX] | N [JH LX] |
| DC-G5 / marked-17 | M13=H | Y [NS SU] | Y [NS SU] | Y [NS SU] | Y [NS SU] |
| DC-G5 / marked-18 | M22=L | U [JH NS] | N [JH LX] | U [NS JH] | U [NS JH] |
| DC-G5 / marked-19 | M22=H | U [LX SU] | Y [CH NS SU] | U [LX SU] | U [LX SU] |
| DC-G6 / marked-20 | M22=H | N [VU XB] | Y [TV] | U [XB TV] | N [XB VU] |
| DC-G6 / marked-21 | M17=L | U [AI VU] | Y [VU TV AI] | U [TV PJ] | U [VU AI] |
| DC-G6 / marked-22 | M17=H | U [TV XB] | U [TV XB] | N [EV MT PJ XB VU TV AI SK] | U [XB TV] |
| DC-G6 / marked-23 | M22=L | Y [AI TV] | U [TV PJ] | Y [TV AI] | U [TV AI] |

## Reproduction and provenance

The public registration preceded the first inference. Each terminal receipt links by hash to one frozen request, and the independent audit crosschecks the three displays and their scores. The marked-versus-filtered primary contrast ranges from -1 to 0 complete layouts across possible completions of missing responses. The registered estimate counts missing responses as failed.

All 72 sessions used the pinned local gpt-oss:20b weights and Ollama 0.40.18, low reasoning, paired record seeds and a 2,048-token generation limit. Elapsed collection time was 35.20 minutes. Direct paid API spend was $0. No model retraining took place. This is a finite circuit-reading experiment with no new Lean kernel check.

The [downloadable ZIP on GitHub](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-marked-reading-audit/research/uriel/experiments/marked-reading-audit/Nous_Marked_Reading_Research_Package.zip) contains the entire study, its SHA-256 inventory and an offline Git history bundle. The PDF and editable TeX are together in the top level of its study folder. It takes only the Python standard library to score the archived responses. From the extracted study folder run:

```sh
python3 -B circuits/check.py
python3 -B pilot/run.py verify
python3 -B pilot/check_displays.py
python3 -B pilot/check_certificates.py
python3 -B audit/displays.py
python3 -B pilot/analyze.py
python3 -B audit/crosscheck.py test
python3 -B audit/crosscheck.py post
python3 -B audit/excluded.py verify
```

[Protocol](PROTOCOL.md) · [72 frozen requests](pilot/order.json) · [Independent audit](audit/post.json) · [Residual errors](audit/excluded.json)

**Human–AI collaboration.** Justin Candler directed the research and specified the three-way comparison. Uriel/Codex constructed and checked the circuits, administered the local model, analyzed the archived responses, and prepared the manuscript.
