# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

## Nous research in this fork

**[Browse all published studies](STUDIES.md)** · **[Publication archive](https://github.com/nousentllc/riemann-hypothesis/tree/32babcca9df1b672cf013625156870bc6947020a/research/uriel/portfolio/publication-archive)** · [Research map and catalog](https://github.com/nousentllc/riemann-hypothesis/tree/research/uriel/research/uriel/portfolio) · [Latest ramified-fiber paper and ZIP](https://github.com/nousentllc/riemann-hypothesis/tree/1da9522e3ada6c5af62c014ea76e77cc40ff3676/research/uriel/portfolio/ramified-companion/paper)

The GitHub file view above opens on `main`, the formalization branch. The study index opens the papers and evidence on their recorded experiment branches without requiring you to switch branches.

## Lean formalization

Build cache for a Lean formalization the proof of the Riemann Hypothesis, and of GRH for Dirichlet L-functions. The first commit is as posted by Levent Alpöge, retrieved on 2026-11-20 at <https://alpo.ge/remark.pdf>.

It has been changed since. Pull requests have deleted files the proof doesn't use, shortened proofs, and
ported it from Lean 4.33.1, which it was written for, to newer releases. The five theorems in
`src/Main.lean` still have the names and types they were published with, and the definitions
those types use, in `src/Statements.lean`, are unchanged. Their proofs are not the published
ones. `git diff --stat 40e56bab HEAD -- src` lists everything that has changed. If you want the
untouched original, check out `40e56bab` or use
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original).

## What is claimed

`src/Main.lean` proves five theorems:

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

[`src/Challenge.lean`](src/Challenge.lean) states the same five with `sorry` in place of the
proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly
those statements, that it uses no axioms other than `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Getting a build

Compiling the project takes hours on a large machine, so there is a cache of compiled files:

```bash
lake exe cache get
lake build --no-build
```

The first command needs Python 3.11 or newer. It downloads Mathlib's cache and then ours. Ours
has to match your checkout exactly. It looks for a successful CI build of the same source
(commits that only change documentation share one) and, failing that, for the baseline build
pinned in [`scripts/cache-baselines.json`](scripts/cache-baselines.json). If nothing matches,
it says so and you are left with `lake build`. The second command confirms that there is
nothing left to compile.

Don't treat the cache as a check of the proof. It contains files built from unreviewed pull
requests on volunteers' machines, and all the download verifies is that you received what was
uploaded. If you need to trust the result, build it yourself as described below.
[CACHE.md](verification/CACHE.md) explains how the cache is made.

## Checking the proof

To check the proof yourself, without the cache, take a fresh clone on a Linux machine with
[bubblewrap](https://github.com/containers/bubblewrap) installed and run:

```bash
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
lake comparator
```

The first command fetches Mathlib's compiled files and nothing of ours. Don't use
`lake exe cache get` here, because that also downloads our prebuilt copy of the submission. The
second reads `comparator.json`, builds `Challenge` and `Main` in a sandbox with no network, and
makes the checks described under [What is claimed](#what-is-claimed).

The build is the expensive part, and compiling the submission runs its code. If you would
rather build in a VM or a sandbox of your own, fetch Mathlib's cache as above, export the two
modules yourself and hand them to Comparator:

```bash
export LEAN_ABORT_ON_PANIC=1        # as Comparator does
export LAKE_ARTIFACT_CACHE=false    # in case cache-env.sh was sourced

# in a clone where the submission has not been compiled
lake build Challenge
lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

# wherever you build the submission
lake build Main
lake env leanexport Main -- $(cat export-targets.txt) > solution.export

# from an empty directory, with the same Lean release and comparator.json from the first clone
lake comparator --config comparator.json \
  --challenge-from-export challenge.export --solution-from-export solution.export
```

The published source was written for Lean 4.33.1, which has neither `lake comparator` nor
`leanexport`, so checking `40e56bab` itself takes two toolchains.
[An older version of this README](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
has those steps.

We don't have a complete run on the current source yet, by either route. On the published
source the build took hours on a large machine and about 100 GB of disk, and judging needs a
lot of memory. [NOTES.md](verification/NOTES.md) says where the source came from, how the tools
and sandboxes are set up and what a passing run does and doesn't show, but it still describes
the Lean 4.33.1 setup.

## CI

Every push and pull request gets a quick check that `Challenge.lean` compiles against Mathlib
alone. A full build is too big for GitHub's runners, so pull requests are built on machines
lent by volunteers, and successful builds go into the cache. If you have a Linux machine with
plenty of memory and disk to spare, [CI-RUNNERS.md](verification/CI-RUNNERS.md) explains how to
lend it. The scripts behind all this are in [`scripts/`](scripts/) and
[`tools/ci_native/`](tools/ci_native/README.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here
so that it can be checked. Commit `40e56bab` is the unmodified copy.
