# Exact circuits for a forced second reading

The calibration table is the complete list of eight settings of three binary switches. Each record supplies a first lamp, the identity of a second meter and its observed lamp. The query concerns signed current on a specified oriented resistor. Both the exact rational current and the truth of the strict threshold comparison can be rendered for each candidate. No hidden actual switch setting is needed to generate or score the problem. Each possible setting in the intersection agrees with all observed facts.

## What the two readings establish

Each fresh network supplies three records. They share their topology, resistors, meter calibrations, eight candidates, row order, target and first observed lamp. The two decisive records give each possible physical reading of the same meter. The third uses a different meter on the same initial candidate set. All three records leave exactly two compatible IDs. A yes or no certificate consists of those two IDs, which agree in their truth value. In the ambiguous case the same two IDs give the unique opposing witness pair. Certificate length and final candidate count consequently reveal nothing about the required verdict.

| Family | Vertices / edges | Observed initial lamp | Decisive meter | If H | If L | Ambiguous observation |
|---|---|---|---|---|---|---|
| DC-F1 | 6 / 13 | H | M7 | Y | N | M4=L |
| DC-F2 | 7 / 13 | L | M7 | Y | N | M8=H |
| DC-F3 | 7 / 14 | H | M7 | Y | N | M2=L |
| DC-F4 | 8 / 12 | L | M2 | N | Y | M3=H |
| DC-F5 | 8 / 13 | H | M2 | N | Y | M7=L |
| DC-F6 | 8 / 14 | L | M8 | N | Y | M5=H |

Alone, either supplied lamp leaves four candidates with both positive and negative truth values. In all 18 records the first lamp alone leaves two of each. Intersecting the two four-element sets gives two states. On each decisive pair, changing the second lamp exchanges the two positive candidates for the two negative candidates. On the ambiguous control, both possible second readings would leave one positive and one negative. Both readings are necessary for the exact certificate even when the final claim remains ambiguous. The case generator checks all readings with rational arithmetic. A lamp is H exactly when its physical measurement is strictly greater than its own threshold. The inversion in the last three networks is a property of the circuit and the chosen target.

For DC-F1 the first lamp H leaves PT, ZD, LE and RK. The signed current of R4 is positive for PT and ZD and negative for LE and RK. Given only M7=L, FS, KK, LE and RK are possible, with FS positive. Intersecting these readings leaves LE and RK, so the warranted verdict is N. Replacing M7=L with M7=H leaves PT and ZD and the verdict becomes Y. Keeping the first reading and instead supplying M4=L leaves ZD and LE, so U requires both witnesses. The IDs are opaque two-letter labels, with a fresh layout-specific ordering. They are distinct across the six layouts and selected outside the historical label pools.

## Electrical reconstruction

The source fixes the supply and ground at 12 and 0 volts. All resistances are positive. With the switches open, the fixed edges still contain a path through all vertices connecting both terminals. Closing any subset of switches preserves connectedness. Kirchhoff's current equations at the internal vertices therefore have a unique solution for every setting. The generator solves the resulting Dirichlet system by exact rational elimination. Current is the start voltage minus the end voltage divided by the resistance on each conducting edge, and zero on an open switch.

The second calculation enumerates all acyclic spanning forests with two components that separate supply and ground. A forest receives the product of the conductances of its edges. The voltage at an internal node equals 12 times the fraction of total forest weight in which the node belongs to the supply component. The check compares every such voltage and the resulting currents against the nodal solution. It also verifies zero net current at each internal node and equality of total resistive dissipation with power delivered at the terminals. Across the 48 settings, the two computations agreed on 352 voltages and 632 signed currents. The independent arithmetic verified 96 meter outputs. Twenty-five target currents are negative, and two equal their threshold, using each physical state just once.

## Why these are fresh but designed cases

The numbers of vertices and edges, counting switchable resistors, are isomorphism invariants even when orientation, terminal labels, resistor values and switches are ignored. The six pairs in the table are distinct and occur in none of the 14 historical layouts. The earlier invariants and both solvers are packaged in the verification files. We reused the prior physical model so that changing layouts did not introduce a second electrical convention.

The generator uses a seeded vertex permutation, a path connecting the two terminals, distinct random chords and three separately switchable resistors. It searches the possible rational comparator thresholds of each candidate graph. A qualifying graph must admit the two-step ambiguity structure and assigned meter polarity. Where several sets of probes qualify, the rule prefers a sign-changing target current and then shorter threshold representations. Ties follow generator order. The published design stores the first qualifying trial for each requested graph size. This purposive search gives matched observations with an exact answer, and makes no claim about how naturally occurring meters divide candidate settings.

In the filtered view the visible two IDs can be copied directly as a candidate certificate. The remaining operation is to decide whether those rows both say yes, both say no, or disagree. In the full view neither individual lamp identifies this pair. The rendered meter names and polarities are fixed design data. An agent inferring a sign from a name or a reading must still supply both jointly admissible IDs. Results across the three records derived from each topology are dependent.

## Reproduce

Run the following from this directory. Each command rebuilds its products in memory and compares them with the archived JSON. Python's standard library suffices.

~~~sh
python3 -B select_panel.py
python3 -B cases.py
python3 -B check.py
~~~

[Selected circuits and thresholds](design.json) · [All 18 paired-reading records](records.json) · [Physical checks and joint observation cells](verification.json)
