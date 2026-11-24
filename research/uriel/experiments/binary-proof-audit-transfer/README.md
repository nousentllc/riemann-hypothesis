# One lookup: from a binary mass formula to a research-agent experiment

**Nous independent research · 24 November 2026.** [Research paper](paper/One_Lookup.pdf) · [Standalone LuaLaTeX source](paper/One_Lookup.tex) · [Binary proof trace](binary/README.md) · [Case-level decision table](pilot/reports/test-gptoss/cases.csv)

We traced the two limits that give scalar one for a single vector in a two-dimensional anisotropic Hermitian space. Then we tested whether a 125-word method drawn from our Lean work changes what a fresh agent can establish when it may request one additional observation. These are separate results.

## What happened on the frozen panel

The proof-derived instructions helped on the formal problems. Both instructions solved the same two circuit records, and neither completed a circuit family. The prespecified decision required a net gain of one family in each domain. We stopped at the pilot.

| Measure | General checklist | Proof-audit method |
| --- | ---: | ---: |
| Complete two-record families | 0/12 | 3/12 |
| Formal families | 0/6 | 3/6 |
| Circuit families | 0/6 | 0/6 |
| Certified cases | 7/24 | 11/24 |
| Correct attainable verdict regardless of certificate | 9/24 | 14/24 |
| Certified determinate cases | 3/16 | 5/16 |
| Decisive measurements selected where needed | 0/8 | 1/8 |
| Unsupported definitive assertions over actual turns | 6 | 5 |
| Unfinished or invalid model turns | 1 | 1 |
| Generated tokens including local reasoning | 13974 | 14473 |
| Cumulative local model service time | 19.05 min | 17.99 min |

There were 3 family wins for the supplied method, 0 losses and 9 ties. On the discordant families the exact paired sign-test p-value is 0.25, and the 95% conditional interval on the direction of a discordance is 29.2%–100.0%. These are twelve deliberately constructed family pairs. The interval is descriptive for this small experiment; no prevalence over research domains was estimated.

The following table assigns each case to the first barrier preventing success. The measurement category includes a record where a guessed final verdict happened to match the hidden state but the observation did not license it. The decision category includes missing output when sufficient evidence was available. The certificate category requires the right visible and attainable verdict.

| Case-level bottleneck | General | Method |
| --- | ---: | ---: |
| Measurement did not settle an attainable question | 8 | 7 |
| Verdict or completion failed despite sufficient evidence | 7 | 5 |
| Verdict right, certificate invalid | 2 | 1 |
| Attainable verdict and valid certificate | 7 | 11 |

All served cases have a public finite candidate universe. Both arms received the same world descriptions, format, materials and lookup budget. The score requires the exact surviving set for a determinate verdict, or a pair of compatible opposing states for an unsettled verdict. This is a stronger requirement than getting the final sign right. The two turns for a session share history. Different sessions begin fresh. [Scoring and controls](pilot/DESIGN.md) · [Paired diagnostic tables](pilot/reports/test-gptoss/lookup_diagnostics.json)

### A case that can be checked by hand

In the second set-union problem, both sessions initially gave the same pair of witnesses. In P the sets were {3} and {2}, whose union has two elements. In J the sets were {3} and {1,2}, whose union has three. The initial evidence allowed both. The checklist session stopped there. The procedure session asked for the size of the second set. The answer, one, eliminated J. The surviving states were P and G, where G had the sets {2} and {0}. Each had a union of size two. The procedure session returned both state IDs and answered the threshold question in the negative. This was the only scored case in which either session used its observation to settle a previously open question. [General answer](pilot/observed/test-gptoss/formal-23_general/session.json) · [Procedure answer](pilot/observed/test-gptoss/formal-23_method/session.json)

The other three additional passes changed the handling of evidence already available. On circuits, each arm certified two of the four permanently ambiguous records and zero of the eight records with a determinate answer available. The packets already supplied all comparator readings and the exact target currents for every candidate. A follow-up on new development cases could add one column giving the result of each current's comparison with the target threshold. Keeping the candidate rows and meter choices identical would help distinguish difficulty interpreting signed fractions from difficulty choosing and applying a measurement. The development gate used here tested whether the model could produce a valid certificate. Its four selected records contained no case requiring an informative lookup.

## What the proof established

Write D=[F:ℚ]. The left argument counts vectors on a lattice in 4D real dimensions and normalizes the unitary average. The right argument sums over represented lengths using the mesh δ=ε². Fiber dilation and integration back over the Gram coordinate recover the same coordinate-Haar test volume. The finite scale quantities use different measures. A common test supplies 0<V<∞, and a separately supplied fiber coefficient κ is shared across the needed lengths. The finite-scale comparison and the two limits then give V=κV and hence κ=1. The finite prime factors outside the selected set have normalized integral one; their values at particular lengths can differ from one. [Source reconstruction and existence steps](binary/README.md)

The pinned source trace covers 45 line ranges in 23 files. All 28 original reconstructed Lean objects matched their published digests byte for byte. Lean 4.33.1 replayed each of them and one positive-test extract. The seven inspected declarations reported only propext, Classical.choice and Quot.sound. The checked archimedean theorem assumes the required family of measures on the fibers already exists and satisfies its disintegration hypotheses. The full binary mass identity and its RH application lie beyond this kernel replay. [Binary kernel receipt](binary/kernel_receipt.json)

An independent four-dimensional test has exact volume 3π²/4. In the raw trace coordinate, omitting the Jacobian doubles the mesh result at every tested scale compared with the same mesh including the Jacobian. Restoring it gives the exact continuum volume on this particular raw trace mesh. The direct length mesh and the vector lattice have their own finite-scale errors. [Finite shell calculation](binary/radial_results.json) · [Artificial local density calculation](binary/density_results.json)

## Trial chronology and limits

The two 125-word instructions and model-selection policy were committed before model trials. Qwen2.5 3B produced eight parseable final development answers and zero valid certificates. The prespecified replacement gpt-oss 20B certified 5/8 development cases. Those eight development sessions per configuration are excluded from the scored results. On a pre-outcome audit, choosing the most varied observation could solve every formal family of the provisional design given a perfect reasoner. We amended four scored-only menus and verified all possible replies before freezing them. The revised shortcut certifies three out of six families per domain under that ideal-reasoning assumption. [Development decision](pilot/development_decision.json) · [Original and revised shortcut checks](diagnostics/README.md)

The fixed gpt-oss 20B model received 56 model calls for 48 scored sessions. Direct API spend was $0; local runtime, hardware and electricity were used. The scorer preserved missing and length-limited calls. Visible outputs, returned observations reconstructable from the pinned records, request hashes and token counts are included. Private internal reasoning was not collected. Local study freeze commit `0732276ad4df6783eb64ea832cb917b29dffc3bb` preceded scored dispatch. An immutable copy of the frozen protocol hashes was posted while the run was in progress. [Fork protocol snapshot](https://github.com/nousentllc/riemann-hypothesis/tree/d7c1fc3d39171fac5686620c4983b1bc60efa06a/research/uriel/experiments/binary-proof-audit-transfer) · [Scored registration](pilot/registry/test-gptoss/FROZEN.json)

The scored cases comprise six finite specializations of distinct Mathlib rules and six circuit topologies, each with a matched pair. For the formal cases, 46 finite target truths across evaluation and development were checked in Lean. For the circuits, independent exact computations agreed on 328 node voltages and 528 branch currents across both sets. The two domains share the same finite observation structure. The study does not measure open-ended proof discovery, effects on model weights, or unaided retrieval in a new session. [Formal cases](formal/README.md) · [Circuit cases](circuits/README.md)

## Reproduce without model inference

From this study directory, the following commands use Python 3.11 or later and its standard library. They need no API key. The original full scoped Lean replays additionally need the pinned SDK, a built Mathlib checkout and a Git checkout containing the source commit; see the binary and formal directories. The ZIP includes the local registration history as a Git bundle and the original project source subset used in the binary audit.

```sh
python3 -B pilot/check_scored_oracle.py
python3 -B pilot/verify_run.py dev qwen
python3 -B pilot/verify_run.py dev gptoss
python3 -B pilot/verify_run.py test gptoss
python3 -B formal/score_views.py
python3 -B diagnostics/audit.py --version revised
```

**Human–AI collaboration.** The human collaborator selected the mathematical direction, asked for an empirical test of benefit to the research system, and authorized this phase. Uriel/Codex designed the comparison, reconstructed the proof, ran the checks, and prepared the report. External mathematical peer review and independent model replication remain open.
