# Can an ambiguity check repair the frozen reader?

**Exploratory addendum after the preregistered results.** The terminal-list reader gave a definite answer on 765 held-out state–queries where its record was ambiguous. Keeping the fitted tree unchanged, an exact arithmetic guard converted all 765 guesses into abstentions. It left the 105 errors on identifiable queries unresolved. A second guard with the same number of abstentions still guessed on 510 ambiguous pairs.

## Independent verification of split, labels and scoring

The [audit program](audit_guard.py) verifies the original result’s hash, decodes its saved trees with a new interpreter and reconstructs tag fibers and answers directly from modular remainders. It imports no training or scoring functions. It reproduces the licensed-action, abstention, hidden-truth, unsupported-definite and wrong-on-determinate totals for all six fitted trees. Running it with CPython 3.9.6 and 3.13.2 produced byte-identical [audit data](audit_guard.json).

- The 12 held-out cutoff values are disjoint from the 52 training cutoffs. The test includes 41,067/42,768 state–queries whose center and weight occurred together in training at another cutoff. The other 1,701 involve weights 59 through 64. There are no unseen centers. These are repeated observations of the same finite arithmetic system under a new cutoff, with no estimate of performance on unrelated memory tasks.
- The coarse model’s 127 distinct ambiguous training observations account for 2,159 training state–queries. The 45 distinct ambiguous test observations account for 765. Each test ambiguity has one compatible yes and sixteen compatible no answers. Reweighting the coarse table by the fiber size gives the same latent-state and query weighting as the lossless record. A deployment that sampled tags uniformly would have different rates.
- Training support labels were supplied by a teacher that can examine the full compatible set. The plain reader saw the decoded tag, cutoff and weight. The informed readers also saw two deterministic transforms of these fields. The terminal encoder was deliberately designed for the known horizon 64. Thus arithmetic structure and the terminal horizon were supplied in advance. The held-out query labels were used only in scoring, and every center in the coarse empty fiber received identical visible features for a fixed query.
- On the lossless tree’s three-matching-digit branch, raw cutoff ≤23 and cutoff band ≤2 agree on all 3,104 training pairs. They disagree on 150/1,056 held-out branch pairs. All 150 are hidden-truth errors of that tree. The feature-order tie rule selected the raw cutoff, which makes this a boundary extrapolation failure under the preset split.

## Exact guard versus a coverage-matched control

For a nonempty terminal tag the center is known exactly. For the empty tag the possibilities are 0 and the integers 65 through 80. For a query (Z,e), let m be the least power of three strictly greater than Z. The number of compatible centers in the empty fiber that satisfy the query is

    h = 1{e ≡ 0 (mod m)} + floor((80−e)/m) − floor((64−e)/m).

The guard withholds the tree’s answer exactly when 0 < h < 17. It uses the visible inputs and the stipulated fiber model, and never uses the unknown designated center. A coverage-matched control uses the same rule with query weight rotated cyclically by floor(Z/2) inside each cutoff. It still asks the original tree about the actual weight. The two rules withhold exactly the same number of queries at every held-out cutoff for the same tag. The rotation is a deterministic negative control, chosen after the primary experiment. Neither rule was trained.

| Terminal-list reader | Withheld | Unsupported definite | Withheld on determinate | Licensed actions / 42,768 | Wrong on determinate |
|---|---:|---:|---:|---:|---:|
| Frozen informed support tree | 0 | 765 | 0 | 41,898 | 105 |
| Same tree and exact guard | 765 | 0 | 0 | 42,663 | 105 |
| Same tree and rotated guard | 765 | 510 | 510 | 41,643 | 105 |

The exact guard gives 41,898 truthful answers out of 42,003 answered queries. The rotated guard gives 41,868 out of 42,003. For comparison, the unguarded tree answers all 42,768 and matches the hidden truth 42,618 times. “Licensed actions” includes required abstentions, so its increase does not mean the number of correct definite answers increased. The full-residue reader receives no guard interventions and still misses all 150 determinate positives identified in the original results.

This experiment identifies where a known observation model can safely override a learned reader. Applying that result in another memory system would require an independent way to specify or bound its compatible hidden states. Nothing in the result shows that the reader learned that model, or that this particular guard handles corrupted witness bindings.

Reproduce from this directory with `python3 -B audit_guard.py > /tmp/changing-cutoff-guard.json` and `cmp /tmp/changing-cutoff-guard.json audit_guard.json`. The preregistered protocol and original results were frozen before this addendum.
