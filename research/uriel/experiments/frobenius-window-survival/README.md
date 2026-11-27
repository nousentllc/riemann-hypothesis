# Frobenius premium in the arithmetic window

Follow-up to the [same-set gain result](https://github.com/nousentllc/riemann-hypothesis/commit/59994e6770c0746f5d4462017b38b1f74af77364). The written theorem jointly selects one prime and orbit in the original weighted host, with the retained set, weights, and lift rules fixed. At that prime the lift-summed premium over the original clipped fallback pays the entire tau and any fixed nonnegative multiple of io, with at least $mb'/4$ left. The original number-field transport produces $2\log p$ in Ga and $\log p$ in IOsum. The chosen witness still has the earlier odd-anchor collision and the row premium at each permitted lift.

The native predecessor sum is paid by distinct even-source minima. A three-endpoint normalized ramp puts the primes in $(X'/3,X'/2)$. The nonleading tau cost and prime-wide interaction are controlled on the same original datum. The local margin by itself gives no guarantee for every prime that passed the earlier test.

## Replay

- [Predecessor](Predecessor.lean) checks the actual backward rule, reduced parity and injective matching.
- [NativeAccounting](NativeAccounting.lean) checks the gain split, the exact tau formula and the prime-wide maximum and ceiling in io.
- [MatchedTau](MatchedTau.lean) checks the capacity comparison for actual predecessor visits and the finite joint-budget step.
- [TentWindow](TentWindow.lean) checks the normalized interior support and original character centering.
- [InteractionBudget](InteractionBudget.lean) extracts the surviving capacity cost bound from WOK and weights the actual interaction.
- [WindowTransport](WindowTransport.lean) checks the numerical gain filter and the native number-field place coefficients.

The [replay receipt](replay_receipt.json) uses Lean 4.33.1 with prepared original imports. The [source trace](source_trace.json) verifies the tapped source files against commit 40e56bab026552e089d7afcfeff08d2defb9c005. The Fourier strip weights and late asymptotic selection are written proofs from those inputs. The experiment does not extract a numerical prime or rebuild the original RH archive.

Run the deterministic exact controls:

    python3 -B controls.py > results.reproduced.json
    diff -u results.json results.reproduced.json

With the original src, a prepared original module tree, Lean 4.33.1 at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and built Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474:

    python3 -B replay.py --source /path/to/original/src --objects /path/to/objects \
      --sdk /path/to/lean-sdk --mathlib /path/to/mathlib --receipt replay.reproduced.json

Compile the single TeX source three times with LuaLaTeX. It embeds the original Nous PNG.

[Manuscript PDF](Frobenius_Premium_in_the_Arithmetic_Window.pdf) · [Editable LuaLaTeX](Frobenius_Premium_in_the_Arithmetic_Window.tex) · [Complete ZIP](Nous_Frobenius_Arithmetic_Window.zip)
