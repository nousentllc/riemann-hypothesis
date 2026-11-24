# Six new circuits for the target-comparison diagnostic

Every record asks whether the signed current on one oriented branch exceeds a specified rational threshold. The public calibration table lists all eight settings of three switches, their target currents, the lamps of three optional meters and the lamp of the initial meter. One observation rules out four settings. The reader may request one additional lamp. The exact target column deliberately makes a circuit solver unnecessary for reading the task. The intervention can append the truth value of the comparison to each candidate row without identifying which setting occurred.

Two records share each network. Only the initial lamp changes in the displayed evidence. The settings, currents, menus, thresholds and table order are identical across twins. All six networks are distinct from the eight layouts in the preceding study even after forgetting both terminal names, resistor values, edge orientations and switch labels. Each new network has a different ordered pair (number of vertices, number of edges). None of these six invariant pairs appears among the previous eight. The physical model again uses ideal signed measurements, a 12 V supply, ideal switches and positive linear resistances. These are purpose-built finite development examples. They sample neither a distribution of commercial circuits nor a population of reasoning problems.

| Family | Vertices | Resistors | First record | Second record | Unique deciding meter on the actionable record |
|---|---:|---:|---|---|---|
| T1 | 5 | 10 | One lookup, yes | Already yes | M7 |
| T2 | 6 | 11 | Stays ambiguous | One lookup, no | M2 |
| T3 | 6 | 12 | Already no | One lookup, no | M8 |
| T4 | 7 | 11 | One lookup, no | Stays ambiguous | M6 |
| T5 | 7 | 12 | Already yes | One lookup, yes | M7 |
| T6 | 8 | 11 | One lookup, yes | Stays ambiguous | M4 |

## What makes a meter decisive

On each actionable record the four compatible settings split evenly on the target claim. Exactly one meter divides them into two same-sign pairs. Its low and high readings both settle the claim. Every other feasible reply on every other meter retains at least one true setting and one false setting. At least two displayed meter columns vary over the initially allowed settings. A poor measurement cannot receive credit merely because the selected physical state happened to give a lucky reading. On the three inherently ambiguous records, every meter and every feasible reply leaves opposing witnesses. The three settled records answer the question before any measurement.

For example, circuit-03 asks whether the current on R7 exceeds −1/6 A. Its high initial lamp leaves four candidates. GL has current −7896/14255 and RX has −4296/21523; both fall below the threshold. UC has a positive current. ZL has −636/7493, which exceeds −1/6 because 6 × 636 < 7493. Two negative currents can therefore give different answers to the same threshold question. M3 divides the candidates into {GL, UC} and {RX, ZL}, both mixed. M6 has the same reading in all four states. M2 divides them into {GL, RX} and {UC, ZL}, which have opposite, uniform answers. Its actual low reply identifies the first pair. The test can score recognition of ambiguity, choice of M2, and the final negative answer with its supporting pair separately.

## Construction and verification

The [layout definitions](network.py) retain the earlier study's exact nodal elimination and its eight historical layout specifications. Six new, connected networks have three distinct switched edges apiece. Thresholds were selected from intervals between attainable physical values and boundary values under a strict greater-than rule. We searched for a target on an internal branch, an initial comparator, and three physically distinct optional comparators meeting the outcome constraints above. We favored cases with signed target currents, informative distractors and feasible variation on the permanently ambiguous twin. The [design file](design.json) freezes the resulting probes and physical switches. These choices were made using exact solver outputs before any reader model was exposed. The deciding meter occupies each of the three displayed positions twice. Fourteen of the 48 target currents are negative and two equal their thresholds exactly. Each equality gives the negative answer to the strict question.

The [records](records.json) are generated using rational nodal analysis. The [independent verifier](check.py) enumerates positive conductance-weighted spanning forests with two roots, one at each fixed terminal. The fraction of total forest weight in which a vertex is connected to the positive terminal gives its voltage after multiplication by 12. The verifier reconstructs all branch currents from voltage differences and compares the resulting public table fields to their encoded values. It checks signed current conservation at each internal vertex and supplied versus dissipated power in each setting. Across 48 physical settings, the two calculations agree on 312 voltages and 536 branch currents. All 144 optional lamp predictions were checked. The decision audit exhausts 61 reachable meter-reply cells over the 12 initial records. The case-by-case cells and signs are in the [verification receipt](verification.json).

A record contains private keys as well as the packet text. Only the formatted public packet, initial lamp and optional requested reply belong in a reader session. In particular, the stored physical setting and list of eligible state identifiers are used for grading. The treatment shows a target truth bit for every setting, including excluded ones. A target bit has a deterministic value before the hidden setting is chosen.

Reproduce both generation and verification with Python's standard library from this directory.

```sh
python3 -B cases.py
python3 -B check.py
```

The first command compares regenerated records with the archived JSON. The second recomputes the complete verification receipt and checks its file hashes. The original circuit package is available in the [previous study](https://github.com/nousentllc/riemann-hypothesis/tree/42b3ce4890b5c6a584af26d34bbc54f177517871/research/uriel/experiments/binary-proof-audit-transfer/circuits).
