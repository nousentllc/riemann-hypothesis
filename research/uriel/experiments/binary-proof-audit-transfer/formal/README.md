# Finite proof records for one further evidence request

This domain tests whether a reader can apply a supplied mathematical rule to the same object across an incomplete record and a follow-up observation. Each public packet names the governing theorem, describes the initial observation, lists all admissible candidate objects and offers three possible queries. Only one query may be taken. A candidate ID stands for a complete concrete set pair, matrix, graph, polynomial, triple of permutations, or word triple. Returning opposite witnesses is meaningful because their mathematical predicates can be evaluated independently of the model.

The eight source files are from Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, the same revision employed in the proof investigation. Six held-out families use different source files and mathematical objects. The two development families use unordered pairs within bins and natural-number pairing. We excluded the original binary mass proof, cyclotomic windows, and arithmetic-reader fixtures. A search of 30 earlier coverage and source-ledger files found none of the eight focal declaration names. That limited check establishes novelty relative to those recorded traces. Public theorem names may be familiar to the models.

| Held-out source family | Query about the underlying object |
|---|---|
| Finite-set cardinality | Does a union meet the size threshold after overlap? |
| Matrix determinants | Does an integer matrix have determinant zero? |
| Graph common neighbors | Do both required edges occur in the same graph? |
| Quadratic discriminants | Is there exactly one rational root of a quadratic with a nonzero leading coefficient? |
| Permutation sign | Is the product of three possibly trivial transpositions odd? |
| Hamming distance | Does the intermediate word attain equality in the triangle inequality? |

Within a family the pair of records differs in one visible initial measurement. Both have the same question, source rule, complete list of alternatives, and menu of queries. A different initial measurement necessarily changes the underlying selected object. There are 35 candidate objects across the six held-out source families and 11 more across the two development families. The twins reuse their family's candidate objects. Parameter changes inside the same family do not count as independent administrations.

For the twelve held-out records, four verdicts are already determined. Four initially ambiguous records admit exactly one informative query. In the remaining four, opposite outcomes are compatible even with the entire joint set of possible responses at the designated object. The eight resolvable items split evenly between yes and no. Each domain type and its answer were checked against the frozen observable alternatives. In the ambiguous group, a putative definitive guess can happen to equal the actual object's truth and still lack support. For a settled verdict the exact surviving state IDs form a certificate. For an ambiguous verdict, any surviving opposite pair certifies the ambiguity.

## Replay and scope

Run the following commands in this directory.

```sh
python3 -B check_views.py
python3 -B verify.py --mathlib "$MATHLIB_TREE" --sdk "$LEAN_SDK"
```

The first check independently rebuilds every initial reading and menu observation from the candidate parameters. The second authenticates each source file against Git, regenerates the finite Lean assertions, compiles them, asks Lean for their axioms and kernel-replays the resulting module. It also exhausts the three possible queries on every record. A pinned and built Mathlib tree and Lean 4.33.1 SDK are needed for the second command. The receipt distinguishes the new kernel-checked target propositions from the Python observation and reachability checks. [Source identities](sources.json) · [Finite propositions](FiniteContexts.lean) · [Replay receipt](receipt.json)

The case generator and verification code are investigator materials and reveal the answers. Agent access should be confined to the public question, candidate table, visible measurement, permitted menu and the authorized reply to its own chosen query. Some finite propositions are proved by reduction, others invoke a Mathlib identity. This study checks mathematical reasoning with a supplied rule. Independent discovery of that rule in a source checkout would require a different test.

## Held-out menu revision before scored outputs

The development run and original generation remain reproducible with `cases.py`. A pre-outcome audit found an unintended clue. For every formal case requiring evidence, only the winning menu column varied across the initially possible objects. Picking a column that varied would solve the lookup without examining the predicate. The scored-only overlay `score_cases.py` replaces one redundant observation in each of the four affected families with a quantity calculated from the same displayed objects. The candidate models, underlying truths, initial views, development rows, and original compiled finite propositions are identical. Different queries now supply different partitions of the candidate set.

In each of the four revised lookup records, exactly **two** queries vary. Exactly one guarantees resolution for every possible reply; the other leaves opposing witnesses alive on the designated reply. A third query remains constant. The guaranteed menu choices are b, a, c and b respectively in the native query IDs. In each of the four irreducibly ambiguous records, every initially compatible object has an opposite-outcome counterpart with matching joint observations, even if the hypothetical underlying object is changed. This removes the single-varying-column shortcut; fixed-choice and other heuristics can still achieve partial success.

Run `python3 -B score_views.py` to independently reconstruct every revised reading, recompute all query partitions and check the 4/4/4 balance, 2/2 sign split in each category and exact development match. [Revised menu receipt](score_menu_receipt.json)
