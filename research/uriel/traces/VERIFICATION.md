# Proof context and verification audit

Inspected 22 November 2026. Original source pin: `40e56bab026552e089d7afcfeff08d2defb9c005`. All code conclusions below concern that pin, read with `git show`; they do not certify the edited community snapshot. No proof build or replay was run by this reviewer.

## 1. Five endpoints, one main theorem

`src/Main.lean` contains five theorem declarations. Two alias `rhOfAll`; one aliases `allChi`; one selects `claimAll.2.1`; one aliases `critAll`. These are five related endpoints, not five independent mathematical discoveries or independent proofs of RH.

The central proposition is `UpperTheory.EveryCharacter`, in `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`, lines 13–14:

For every nonzero natural modulus N, every complex Dirichlet character chi modulo N, and every complex s, if Re(s)>1/2 and either chi is nontrivial or s is not 1, then L(chi,s) is nonzero.

The explicit s=1 exception for the trivial character concerns a pole and Mathlib's total-function conventions, not a missing region of the classical theorem. The final GRH scope is Dirichlet L-functions. The checked headline statements do not prove the corresponding results for general Hecke, Dedekind, or automorphic L-functions.

The code in `src/Statements.lean` imports only Mathlib. The RH statement explicitly excludes negative even integers and s=1; the Dirichlet strip statement assumes 0<Re(s)<1. The external Audit.lean also checks definitional equality between the custom RH alias and Mathlib's RiemannHypothesis.

## 2. Exact closing chain inspected

1. `src/Main.lean`: the public aliases.
2. `src/Supplements/Kernels/MainTheorems.lean`: `allChi` is `UpperTheory.FinalTheorems.everyCharacter`; RH, strip, and primitive-strip consequences are derived from it.
3. `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`: `everyCharacter_of_row` supplies an OpenLiteratureStatements record from a row hypothesis and `recTExists`, together with `vwin_of_row h`. `everyCharacter` instantiates the row with `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`.
4. `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`, line 6: `galoisLocalGlobalStrong_recParameter` is obtained from `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`.
5. Adjacent `GaloisRepresentationsOfThetaLift.lean`, line 6: this passes `UpperTheory.Gal.Int.Geo.geoOne_holds` and the theta-lift input to `galoisLocalGlobalStrong_of_geometry_lift`.
6. `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean`, lines 4–5: the concrete theta-lift proposition is supplied by `UpperTheory.TP.tLift_holds_k`.
7. `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`, lines 4–5: the window package is constructed using the row, `OpenImageCondition.mk h`, and `baseChangeN`.
8. `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, lines 810–813: the final assembly passes eigen/local theorem packages, theta-integral matching, a self-intersection/covolume package, local-Langlands existence, and VWin to `every_character_of_theta_integrals_local_matching`.

Items 4–6 are visible constructor connections, not an independent reconstruction of their deeper geometry. The final assembly file has 814 lines, many imports and record-field assignments; reading only its last theorem gives its interfaces, not the proofs of every field.

The local-Langlands existence input is not left as an anonymous unfilled record at the top. In `Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`, lines 20–66, `recTExists` obtains Artin and cuspidal data, constructs an extension, and fills dimension, character, Langlands, cuspidality, twist, central-character, duality, injectivity, depth, and type fields using named subproofs. Those subproofs still need mathematical reading for explanation; the external end-to-end dependency audit is the evidence that no extra axiom remains in the headline result.

## 3. Reflection is real content, although it is not the novel arithmetic core

`CharacterBoxes/ClaimStrip.lean` contains a complete short proof of the transfer from a right half-plane conclusion to all zeros in the critical strip:

- `factor_ne_zero`: for Re(s)>0, each missing Euler factor 1-psi(p)p^(-s) is nonzero because |psi(p)|<=1 and p^(-Re(s))<1.
- `prim_zero`: the change-of-level identity therefore passes a zero of an imprimitive Dirichlet L-function to its primitive character.
- `gamma_ne_zero`: the archimedean Gamma factor is nonzero when the real part is positive, treating even and odd characters separately.
- `prim_reflect`: the primitive completed-L functional equation passes a zero at s to a zero of the inverse character at 1-s.
- `strip`: a zero with real part below 1/2 would thus produce a zero above 1/2; a zero already above 1/2 is directly excluded.
- `zeta`: the trivial character of modulus 1 gives the zeta conclusion in the strip; existing zeta nonvanishing on Re(s)>=1 and the completed-zeta functional equation handle the rest, with explicit treatment of 0 and the negative even trivial zeros.

`Formalism/GammaFactorNonvanishing/CritLine.lean` supplies the parallel primitive-character route used by `critAll`, and `rh_of_every` specializes to modulus 1.

This prevents the loose description that 'symmetry alone proves the left half.' The code needs the primitive transfer, Gamma nonvanishing, the appropriate completed functional equation, and pole/trivial-zero exclusions.

## 4. Imported code is not identical to proof dependence

`MainTheoremsAll.lean` imports `MainTheoremsCritical` and a small-class-number consequence `CorGKOf`. The headline proof terms inspected do not explicitly reference `corGK`. One cannot count every imported source as mathematically necessary to RH, or infer that every consequence discussed in the announcement lies on the RH proof's actual dependency path.

This distinction is visible in the published checks: the full loaded environment has 2,701,132 constants and 2,084,256 theorems, whereas the exported solution has 1,468,418 declarations. The export contains the dependency closure of the five theorem targets. These figures count different things and should not be compared as a simplification ratio without additional analysis.

## 5. External verification, freshly checked

Primary page: https://math.mit.edu/~drew/grh/ (last updated 2026-11-22 16:20 UTC).

- Published original source: all 175,187 Lean modules compiled on Lean/Mathlib 4.33.1.
- Module replay: all accepted by Lean kernel; all compiled modules also passed lean4lean (five required raised resource limits).
- Full exported proof: accepted by independently implemented nanoda and current con-leche; con-ron also accepted all solution declarations during comparison.
- Endpoint identity: con-leche and con-ron independently matched the five theorems against a separate challenge built from Mathlib definitions.
- Axiom dependence: only propext, Classical.choice, and Quot.sound for each headline theorem.
- Reproducibility: a separate sandboxed build reproduced the exported proof byte for byte.
- Remaining on that page: additional whole-export Lean default/paranoid runs and end-to-end Comparator runs were still in progress. This is additional checking, not the absence of a completed Lean module replay.

The audit environment does contain `sorryAx`, compiler-related axioms, and other Lean core axioms. They are not reported as dependencies of the five results. The challenge intentionally represents the five targets as placeholders; comparison checks that the actual solution justifies them. Reporting 'no sorry anywhere' would be false.

The joint Lean/Mathlib statement of 21 November explicitly endorses the statement and proof. That is strong external evidence. Our source reading is not a new independent machine verification, and these checks concern the original submission, not every later community edit.

The source's Mathlib dependency is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`; the original toolchain is `leanprover/lean4:v4.33.1`. A newly edited or migrated proof requires checks appropriate to its own commit.

## 6. What the announcement establishes about interpretation

The announcement gives a mechanism narrative: Stepanov-like multiplicity, repeated theta lifting between definite unitary groups, lift length on a square-root scale, divisibility against size, and additional averaging to control a cost barrier. It explicitly warns that its timeline and technical summaries may need revision because the author had not mastered all the higher-rank mathematics involved. Consequently, it is primary evidence for the author's account, but not sufficient evidence that any particular formal declaration implements an interpretation we choose.

Formal correctness, the historical route of discovery, and a compact conceptual explanation are separate evidential questions. The external checks strongly address the first. The source traces above partially address the third. The announcement is a provisional account of the second and third. A full narrative of the novel arithmetic mechanism still requires reading the actual constructions and bounds, not just assembling the named interfaces.

## Citation handles for parent retrieval

- https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
- https://math.mit.edu/~drew/grh/
- https://math.mit.edu/~drew/grh/audit.log
- https://math.mit.edu/~drew/grh/Audit.lean
- https://math.mit.edu/~drew/grh/con-leche-compare.log
- https://math.mit.edu/~drew/grh/con-ron-compare.log
- https://alpo.ge/remark.pdf
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html (current documentation, not the original pinned file).

Every web page above carries a 200-word source-use budget in the search output. Parent should open sources before citing child refs, per tool instructions. The arithmetic/source analyses here rely on local pinned code reads rather than claims extracted from later exposition.
