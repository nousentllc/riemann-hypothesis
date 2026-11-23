# A zero and the prime windows
All original Lean references use the Riemann fork commit 40e56bab026552e089d7afcfeff08d2defb9c005. The scientific scope is the Dirichlet-character family window implication. The manufactured signals are Laplace-transform models; the measured prime-power functions are separate actual singleton observables. The positive-mass lower exponent and quantifier statements are recorded in WindowMass.lean. No real zero off the critical line was observed or inserted into actual primes.

## Local reproducibility
Run `python3 -B reproduce.py` at the root of this archive, using Python 3.11 or newer. No third-party packages are required. All exact integer and interval receipts must match. For float-only diagnostic values the runner compares with relative tolerance 2e-10 and absolute tolerance 2e-13 to accommodate platform libm differences. Meta-data and exact endpoint strings must match without tolerance. The original run used CPython 3.13.2 on Apple silicon.

With the read-only original tree available also pass `--source /path/to/original` to authenticate the 22 arithmetic source files and all listed line spans. For both kernel replays pass `--source`, `--objects`, `--mathlib` and `--toolchain` with the original source root, directory holding the authenticated original project .olean imports, built Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, and Lean 4.33.1 SDK, respectively. The expected project object digests are packaged in analytic/ and arith/. Instructions for generating original analytic objects with the matching paths and toolchain are in the previous source-pinned record: https://github.com/nousentllc/riemann-hypothesis/blob/b616d08a805e05e358ad0d2b3cd7b180e058a19e/research/uriel/experiments/second/README.md . No generic full Lean build is assumed. The source-tree Git pin is also in both manifests.

The first new supplement formalizes four analytic consequences including the full suffix-power obstruction. The second module assumes the arithmetic supply and compatibility, replays its passage to the analytic theorem, and checks two exact rescaling thresholds. Its 30 authenticated dependencies overlap the 28 authenticating the first module; neither receipt claims a full upstream arithmetic or RH build.

## Study files
- models/PROTOCOL.md records the primary model predictions. models/probe.py implements phase-clipped mass, signed cancellation, gamma concentration, derivative tests and the analytic spike train. The delayed-onset control and the exploratory arithmetic width extrapolation are supplementary.
- primes/protocol.json and primes/prime_mass.py give the primary bounded windows, normalization and directed enclosures. The closed-integral check in primes/chi4_closed.py uses a separate integration and prime-power representation and shares elementary certified log and normalization routines with the first calculation. See primes/SUPPLEMENT.md for post-registration order.
- arith/protocol.md, arith/check_arithmetic.py and arith/control_receipt.json describe the same-index, whole-window and comparison counterfactuals. The arithmetic width follow-up proves a local interval-fit assertion only.
- analytic/WindowMass.lean, arith/ArithmeticWindow.lean and their receipts delimit the kernel claims.
- build/figs.py regenerates three vector PDFs with ReportLab from the archived results. This step is optional; the manuscript already embeds the figures.
- SHA256SUMS addresses the files extracted from this archive. Use the original TeX file and LuaLaTeX for the paper itself.

