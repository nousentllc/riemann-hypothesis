# Six physical circuits for three displays of the same evidence

The 24 records encode six resistor networks, three binary switches per network and two observed comparator lamps per record. The unknown switch setting ranges over eight possibilities. The question asks whether signed current through one specified resistor strictly exceeds its threshold. The eight possibilities and their threshold labels are fully specified in the calibration table. Records deliberately contain no designated hidden setting. An answer must hold across all settings consistent with both lamps.

## How one network produces four records

The first comparator and its reading stay fixed across the quartet. It leaves four candidate settings, two above the target threshold and two at or below. Two other calibrated comparators serve as alternative second observations. Both possible readings of each appear in the panel. One comparator splits the four candidates by their threshold labels. Its two readings require opposite verdicts. The other splits the same candidates into opposite-label pairs. Its two readings require the same ambiguity verdict supported by disjoint pairs of IDs.

On G1 the initial reading leaves DA, KF, SY and BU. M11 low leaves DA and KF, both at or below the threshold. M11 high leaves SY and BU, both above. M19 low leaves DA and SY, whereas M19 high leaves KF and BU. A reader that answers “undetermined” on both M19 records has given both warranted verdicts. Reusing the first supporting pair on the second record would still fail the certificate check. The same test can be applied to every circuit in the table.

| Layout | Vertices / edges | Initial reading | Decisive meter | Verdict at low / high | Mixed meter |
|---|---:|---|---|---|---|
| G1 | 6 / 14 | H | M11 | N / Y | M19 |
| G2 | 7 / 15 | L | M16 | Y / N | M22 |
| G3 | 8 / 15 | L | M22 | N / Y | M21 |
| G4 | 9 / 11 | H | M22 | Y / N | M17 |
| G5 | 9 / 12 | H | M13 | N / Y | M22 |
| G6 | 9 / 13 | L | M22 | Y / N | M17 |

The counterfactual pairs share layout, table order, thresholds, initial observation and choice of meter. Within either pair only its second reading changes. Either lamp alone leaves exactly four settings including both target labels in all 24 records. Their intersection leaves exactly two. Every mixed-meter pair and every decisive-meter pair partitions the four initial candidates into two disjoint two-element sets. Every layout has four distinct surviving sets. Within a layout and a record, the same physical facts underlie all three displays.

## Selection, independence and provenance

Each network starts as a simple path through the terminals and every internal vertex. The generator adds distinct chords and assigns the final three edges to switches. The fixed edges include the entire path for every proposed size. A positive conductance connects every internal node to both voltage terminals even when all switches are open. Dirichlet voltages are therefore unique for every setting. Resistor orientation sets the reference direction for the reported current.

The search enumerates comparator cuts with four high and four low readings and selects the first qualifying graph from a fixed seeded sequence for each size. Its ranking prefers an internal fixed branch whose signed current crosses zero, followed by shorter threshold representations. Strict inequality matters. Three of the 48 target currents equal their threshold and take the negative truth label. Twenty-three physical target currents are negative in their specified orientation. A negative signed current can still exceed a negative threshold.

The ordered pair (number of vertices, number of edges) is preserved under graph isomorphism. All six such pairs differ from each other and from the 20 networks used in the three predecessor panels. The 48 opaque state IDs also differ from all 160 earlier IDs. The historical ID list was exported directly from the first two panels' ID maps and the last panel's records, indexed by layout. Reproducibility starts at the archived predecessor. [Previous study and provenance](https://github.com/nousentllc/riemann-hypothesis/tree/03854270b77458b2b8f30e74049c142d9bb3c3a1/research/uriel/experiments/forced-reading-audit)

The selection procedure intentionally searches for networks with this exact logical structure. The six networks supply six paired layout comparisons. Within each layout the four records share the same eight switch states. A record-level success count describes performance on these particular questions. It does not convert the panel into 24 independently sampled physical layouts.

## Independent physical verification

The first solver constructs the conductance matrix and solves Kirchhoff's internal current-balance equations using rational Gauss–Jordan elimination. The second enumerates spanning two-component forests that separate the source and ground. Each forest is weighted by the product of its conducting edges' conductances. Dividing the forest weight placing a vertex with the source by total admissible forest weight gives its normalized Dirichlet voltage. Multiplication by the 12-volt supply recovers the physical voltage. Both algorithms use exact rational numbers.

The independent audit rebuilt all 384 node voltages and all 640 oriented branch currents across 48 physical states. It checked internal current conservation, source power against total resistive dissipation, the two meter predictions for each state (96 predictions), every exact target current and lamp, and every survivor set. These are numerical solutions of a specified finite family of linear networks. The logical answers on this panel follow by exhaustive intersection.

## Reproduction

Run these commands from the study directory with a recent Python 3 installation. All use the standard library. Each rebuilds the relevant object and compares it with the archived version.

```sh
python3 -B circuits/select_panel.py
python3 -B circuits/cases.py
python3 -B circuits/check.py
```

[Network designs](design.json) · [Model-facing record fields and scoring sets](records.json) · [Independent reconstruction and controls](verification.json) · [Earlier opaque IDs](historical_ids.json)
