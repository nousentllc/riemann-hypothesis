# Can a trained reader recognize when its saved record is ambiguous?

On 42,768 held-out witness–query pairs, a small trained reader gave the true answer 99.65% of the time and made an unsupported definite claim on **every one of the 765 pairs that required abstention**. In 720 of those 765 cases its guess happened to be true. Giving the reader explicit examples of when to abstain during training did not make it generalize that behavior to the held-out cutoffs. Retaining the full residue eliminated all 765 information losses, but the trained reader still missed 150 positives.

## What was written, and what was learned

Choose a designated center residue s between 0 and 80 and write a seven-bit tag. The terminal-list tag stores the single matching weight at cutoff 64, or zero when the list is empty. Seventeen centers (0 and 65 through 80) produce the same empty tag. The residue tag stores s itself. Neither encoder knows the future query. The records use 65 and 81 of the possible bit patterns respectively. Any binding between a tag and the designated center is a separate assumption.

At query time the reader receives the tag, a cutoff Z and a weight e with 1 ≤ e ≤ Z. The individual truth being predicted is the strict local-center proximity condition

    v₃(s − e) > floor(log₃ Z), equivalently s ≡ e modulo 3^(floor(log₃ Z) + 1).

Zero difference has infinite valuation. Both forms were implemented separately and checked on all 168,480 state–query pairs. The support oracle evaluates the answers for every center compatible with a tag. When these answers disagree, its action is abstention. The local test suite also compares all 81 terminal lists against the earlier archived enumeration. The centers here are possible inputs. The tests never identify the formal proof's designated center, its other two coordinates or a full exceptional set.

Each of the two records was read by three separately fitted depth-limited decision trees. The plain tree learned yes/no/abstain from tag, cutoff and weight. An informed tree received the same supervision plus the base-three power band of the cutoff and number of matching low ternary digits of the visible tag and weight. A third tree used those informed features with individual binary truth labels. No reader saw a hidden center beyond the contents of its own tag. The arithmetic transform supplies prior mathematical knowledge. Neither the encoder nor a language model was trained. Cutoffs 24–29 and 59–64 were withheld in their entirety. Training contained 125,712 state–query pairs at the other 52 cutoffs. Every center appeared in both portions; the test concerns generalization to cutoffs within this prescribed task.

## Held-out results

Every row covers the same 42,768 state–query pairs, weighted uniformly. A licensed positive or negative is a definite answer supported for every center that could have produced the observed tag. For the coarse tag, the 765 ambiguous pairs correspond to **45 distinct observations**, each shared by 17 centers. For each such observation one center answers yes and sixteen answer no. Counts of unsupported claims are weighted by hidden state so that the two records can be compared on identical examples.

| Record and reader | Licensed yes | Licensed no | Definite guesses on ambiguous pairs | Withheld | Hidden truth matched / answered |
|---|---:|---:|---:|---:|---:|
| Terminal list, exact support oracle | 633 | 41,370 | 0 | 765 | 42,003 / 42,003 |
| Terminal list, raw-input tree | 0 | 41,370 | 765 | 0 | 42,090 / 42,768 |
| Terminal list, informed support tree | 528 | 41,370 | 765 | 0 | 42,618 / 42,768 |
| Terminal list, informed binary-truth tree | 528 | 41,370 | 765 | 0 | 42,618 / 42,768 |
| Residue, exact support oracle | 678 | 42,090 | 0 | 0 | 42,768 / 42,768 |
| Residue, raw-input tree | 0 | 42,090 | 0 | 0 | 42,090 / 42,768 |
| Residue, informed support tree | 528 | 42,090 | 0 | 0 | 42,618 / 42,768 |
| Residue, informed binary-truth tree | 528 | 42,090 | 0 | 0 | 42,618 / 42,768 |

Always answering no attains 98.41% truth accuracy and misses all 678 positives. Always abstaining matches the licensed action on 765 terminal-list cases and zero residue cases. On the terminal list, the informed support tree matched the licensed action on 41,898/42,768 (97.97%). It answered no on all 45 ambiguous observations. An optimal forced guesser on this distribution could match truth on at most 42,723/42,768, since the minority on every one of those observations is indistinguishable from its majority. The informed reader made 105 additional errors on identifiable cases.

## Where the generalization failed

| Weight 11, designated center | Saved terminal tag | Truth at Z=64 | Truth at Z=26 |
|---|---|---|---|
| 0 | Empty | No | No |
| 65 | Empty | No | Yes |

At cutoff 64 one needs agreement modulo 81. Every center compatible with the empty tag licenses **no** for weight 11. At cutoff 26 one needs agreement modulo 27, and 65 − 11 = 54 is divisible by 27. The same tag now requires **abstain**. With the residue tag, 65 licenses **yes**. All six trained trees returned **no** in all four rows/cutoffs represented above. The stored case traces give the reader, truth and support decisions individually.

The informed residue tree contains a branch for exactly three matching low ternary digits. It learned a split at raw cutoff 23. In the training data, that split classifies these examples just as well as a cutoff-band split corresponding to Z ≤ 26. The registered feature tie rule prefers the raw cutoff. Cutoffs 24, 25 and 26 consequently produced 48, 50 and 52 false negatives. There were zero hidden-truth errors at the other nine held-out cutoffs. On the terminal-list tree, abstention leaves do exist on the training side of a raw cutoff 23 branch. They are unreachable for held-out cases. The negative result therefore has a particular mechanism in these fitted trees. It does not determine how other tree features, sampling or objectives would perform.

H1's predicted ambiguity with high truth accuracy occurred; the ambiguity was already known from the preceding census. H2 failed, with a tie at 765/765 unsupported definite answers between the informed support and truth readers. H3 held on this split, with informed support recovering 528/678 licensed residue positives (77.88%) against 0/678 for plain support. For the terminal list the corresponding counts were 528/633 (83.41%) and 0/633. This is an exhaustive result for the named population and models, without a sampling confidence interval.

## Controls, provenance and replication

- Reorder held-out records and queries and rename every tag through a known invertible codebook. All three models kept their predictions on all 42,768 pairs per record. This exercises correct decoding when the codebook is supplied.
- Substitute the genuine-looking record for center 2 when the designated center is 1 and vice versa. In each channel, both informed trees and the exact oracle changed 48 previously licensed answers into wrong ones among 1,056 paired queries. A truthful record attached to the wrong witness can reverse the answer even for the oracle.
- The earlier [cutoff census](../research-assessment/check_cutoffs.py) gives the finite arithmetic contract. [The pinned terminal fixture](https://github.com/nousentllc/riemann-hypothesis/blob/4b1c9fbbfb9bc50a3f791c2c1f3d7f2adb336c87/research/uriel/experiments/slot-three/results/weights.json) is checked by Git object ID in the local tests. The binding experiment instantiates the distinction between recoverability and permission to answer in [the local provenance study](../../nous_provenance_study/papers/part_I.tex) and [the memory architecture audit](../../Uriel_GEMA_Formal_Architecture_Audit.md). This is an independent CPU experiment on a finite local predicate. No Lean kernel check or actual witness extraction was performed here.
- A [subsequent exploratory audit](GUARD_AUDIT.md) replayed the saved trees and tested exact ambiguity gating against a coverage-matched control. A new, preregistered follow-up could compare raw-cutoff ablation versus explicit power-band splits, keep the same held-out blocks, then add a fresh cutoff horizon. This would distinguish boundary extrapolation from structural checking of which centers share a record. No model was retuned after this result.

[Preregistered design](PROTOCOL.md) · [Training and evaluation](run.py) · [Tests](test_reader.py) · [Counts, per-cutoff confusion tables, case traces and fitted trees](results.json)

From this directory in the project mirror, run:

```sh
python3 -B -m unittest -v
python3 -B run.py > /tmp/changing-cutoff-reader.json
cmp /tmp/changing-cutoff-reader.json results.json
```

Only the Python standard library is required for training. The provenance test additionally needs Git and the sibling pinned checkout. Protocol and preceding-census hashes are checked at startup. Runs were compared on CPython 3.9.6 and 3.13.2.
