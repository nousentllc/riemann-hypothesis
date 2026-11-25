# External reading and the ramified control

Read sections 21–23 of the [complete paper](../Uncapped_Growth.pdf). The first twenty sections are the expanded study released at 12695d4. The dated supplement is a written deduction and finite replication. All mathematical Lean sources are identical to that release.

| Source | What it settles for this study |
|---|---|
| [Jonathan Hanke, §3](https://www.jonhanke.com/Hanke--all_papers__as_of_2015-01-14/explicit-bounds-paper.pdf) | Prior art for good-type lifting, bad-type reduction, primitive stability and the zero-type scaling factor. Supports a five-digit primitive cutoff for this diagonal form. |
| [Katherine Thompson, §3.1](https://arxiv.org/pdf/1610.06935#page=6) | Independent published four-square benchmark in the real quadratic case with d = 2 modulo 4, including Q(√2). |
| [He and Yang](https://arxiv.org/abs/2407.09076) and [Griffiths](https://arxiv.org/abs/2602.21070) | Unramified dyadic density formulas and explicit lifting over Z₂, respectively. Their base rings delimit direct comparison. |
| [Zhang’s preliminary note](https://www.ihes.fr/~rzhang/files/GRH%20note.pdf), [declaration atlas](https://nasqret.github.io/riemann-rev/atlas/), [Sutherland’s dossier](https://math.mit.edu/~drew/grh/) | Classical provenance, evidence-labeled proof transitions and replay evidence for the original archive. |
| [Community field removal](https://github.com/leanprover-community/riemann-hypothesis/pull/398/files) and [pinned norm identity](https://github.com/nousentllc/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BigThetaNormEqRallisInnerProduct.lean#L19-L37) | The diff drops a Rallis hypothesis field. The original norm proof still builds a nonzero coefficient and calls a specialized Hecke identity with a bundle. Identifying individual downstream projections is a further question. |

Run the following from the extracted study directory.

~~~sh
python3 -B verify.py
~~~

[Finite protocol](PROBE.md) · [Exact executable check](ramified_probe.py) · [Full counts and independent controls](ramified_results.json)

The second ring encoding reproduces every full and all-divisible bin at depth five. The script checks both ranks and all bins through depth ten. The argument for every subsequent depth is written in the paper. The local-density-to-Lean-measure identification for this ramified example remains open in this study. The bibliography is a targeted primary-source search, not a claim of worldwide novelty.
