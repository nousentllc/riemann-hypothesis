# One measurement in a resistor network

These packets test whether a reader can use the evidence it has, choose a measurement that will settle an open question, and recognize the cases in which every available measurement still leaves two physical explanations. A reader gets a source-to-ground circuit, eight switch settings, a table of instrument calibration, one observed reading, and a menu of three comparators. Its question concerns a named branch current. The calibration table keeps exact arithmetic available to both arms and lets either arm focus on the decision.

## What the oracle computed

Each resistor has a positive integer resistance. The two terminals are constrained to 12 and 0 volts. Each of the three switches independently opens or closes a named resistor. For each complete setting, nodal elimination solves Kirchhoff's current balance over exact rational numbers. Current refers to the orientation printed for each edge. “Above” is strict, and equality produces the low reading. Each state also has a two-letter identifier assigned before forming the cases. The table presents every setting, including ones excluded by the observed reading.

Every pair of records has identical circuitry, values, menu, target, table, and set of hidden possibilities. The only changed visible fact is a high/low reading from the same initial meter. The constructor uses different compatible physical states to realize these two readings. Reader-visible files must contain only the description, observed initial evidence and menu. The state chosen by the administrator, compatible-set list, truth labels and eligibility classes belong to the scorer. They are present in this source release for reproducibility.

| Panel | Layouts | Records | Already settled | One decisive lookup | Ambiguous after any lookup |
|---|---:|---:|---:|---:|---:|
| Development | 2 | 4 | 2 | 1 | 1 |
| Held out | 6 | 12 | 4 | 4 | 4 |

All eight layouts have different numbers of vertices and/or edges, counting each separately switchable resistor as an edge. None uses the illustrative pair of equal switchable source-to-ground branches. In the held-out panel, the already-settled records divide two yes and two no. Those requiring a lookup also divide two yes and two no. Each one-lookup record has exactly one comparator that decides the question for either possible reply. In an irreducibly ambiguous record, every available reading with a nonempty compatible set admits both answer signs. This prevents the hidden physical state from turning an intrinsically poor measurement into a good one by luck.

## A development twin

Both DC-D1 records ask whether the current through R2 exceeds 7/2 amperes. The initial comparator measures whether the voltage at node a exceeds 6 volts. A low reading leaves EK, LH, NF and RO; all four lie at or below the target threshold. A high reading leaves BW, CD, EP and OK; only CD and EP exceed the threshold. Under the second record's observation, M5 and M3 retain all four settings. M7 splits them by answer. Its observed low reply leaves CD and EP, certifying yes. Before that reply, a pair such as BW and CD demonstrates why an immediate yes would have exceeded the evidence.

In development record DC-D2/1, even an informative M7 reply leaves FY, MJ and PK. FY and MJ give opposing answers, so identifying the actual switch setting is unnecessary to establish underdetermination.

## Verification

Run from this directory with Python 3.11 or later and its standard library.

```sh
python3 -B check.py
```

The [receipt](verification.json) records 64 physical settings, 328 node voltages, 528 branch currents and 192 public menu predictions. An independent implementation enumerates every conducting spanning forest with exactly two components, one rooted at each terminal. It weights each forest by the product of its edge conductances. The fraction of total weight in forests attaching a node to the 12 V terminal, multiplied by 12 V, reproduces its voltage. This computation uses no elimination routine. The test also reconstructs the packet entries, verifies zero net current at all internal nodes, compares supplied and dissipated power, and enumerates all nonempty outcome cells for each lookup. The request budget is one measurement; two or three lookups can provide information outside this experiment.

The result is a finite decision task over fully specified passive linear circuits with ideal instruments. It measures record use and evidence selection within those cases. The archive includes the deterministic fixture parameters in [design.json](design.json), the circuit and solver definitions in [network.py](network.py), and the panel construction in [cases.py](cases.py).
