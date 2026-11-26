# Comparing the two proof interfaces

[Read the paper](Comparing_the_Two_Proof_Interfaces.pdf) · [Edit the single LuaLaTeX source](Comparing_the_Two_Proof_Interfaces.tex) · [Download the complete ZIP](Nous_Proof_Interfaces_Critical_Edition.zip) · [Read the 16-edition audit](PORTFOLIO_AUDIT.md)

This joint critical edition revises *Where the Two Proof Interfaces Meet* and *From Arithmetic Windows to a Prime Remainder*. At a fixed positive exponent slack, any prescribed positive coefficient works in the readable one-sided bound after a threshold depending on that choice. The [new Lean corollary](Coefficient.lean) uses the actual readable remainder. At target four the original lattice has mass 257/128 under scalar Haar and 257/256 after matching the readable split with fixed vector source. The integral trace-one axiom remains obstructed. A separate readable regular candidate has that lattice value if it meets the stated local integral and continuity hypotheses.

The manuscript derives a fixed-exponent floor estimate, gives controls for the principal Euler correction, and explains how the fixed-host prime classification changes the earlier open witness question. Its source-level and numerical claims are distinguished throughout. The [original architecture study](../window-remainder-architecture/), [first interface note](../upstream-interface-comparison/), [Haar calculation](../target-four-haar/), [square-dilate theorem](../ramified-square-dilates/) and [expanded witness study](../fixed-datum-host-expanded/) retain their original files.

## Fast reproduction

Extract the ZIP into an empty folder and run the following command there with a standard Python 3 installation.

~~~sh
python3 -B verify.py
~~~

This verifies the internal SHA-256 inventory and reruns six finite programs. It takes no model calls and uses no network. The comparison checks exact rational coefficients and counts. The earlier analytic controls also include approximate logarithms in their output. The portfolio inventory records Git revisions and SHA-256 values for the 16 audited PDFs. To compare them with their historical blobs, pass the path of a checkout containing those revisions to the optional --repo argument of verify.py. The earlier PDFs are linked in the audit.

## Lean evidence

The verification records in [replays](replays/) were produced for this edition. The copies under [evidence](evidence/) preserve the supporting modules and original controls from the earlier publications. The broader 108-module square-dilate replay and six-module fixed-witness replay are cited from their releases. The full original RH project and full readable project were outside the current build. Compiled libraries and the Lean distributions are external prerequisites.

The original source pin is [40e56bab](https://github.com/nousentllc/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005), on Lean 4.33.1 and Mathlib 0df444a3. The readable pin is [e063a923](https://github.com/leanprover-community/riemann-hypothesis/tree/e063a923620ee7787b4a1270421478645bf66bdb), on Lean 4.35.0 and Mathlib 56a00585. The architecture script checks the source trace and compiler revisions before elaboration. For the Haar run use the original compiled study library that supplies DilateStableOddAll and DilateEndpoint. The first attempt to replay the original analytic selection used a smaller cache containing the local-density dependencies. It lacked LandauZeroFreeCriterion. The original analytic replay used the prepared original project library instead.

The following commands use example relative paths for those prepared installations. The study library also supplies RamField. The original library argument is the root of the compiled project modules, not the Mathlib root.

~~~sh
python3 -B evidence/architecture/replay.py --mode all --old-source ../original \
  --old-objects ../original/.lake/build/lib/lean --old-mathlib ../original/.lake/packages/mathlib \
  --old-sdk ../lean-4.33.1 --readable ../readable --new-sdk ../lean-4.35.0 --receipt architecture-run.json
python3 -B check_coefficient.py --readable ../readable --sdk ../lean-4.35.0
python3 -B evidence/interface/replay.py --original ../original/src --sdk ../lean-4.33.1 \
  --mathlib ../original/.lake/packages/mathlib --objects ../original/.lake/build/lib/lean --study ../dilate-objects
python3 -B evidence/density/replay.py --lean --sdk ../lean-4.33.1 --mathlib ../original/.lake/packages/mathlib \
  --objects ../original/.lake/build/lib/lean --study ../dilate-objects --receipt haar-run.json
python3 -B evidence/density/replay.py --valuation-lean --sdk ../lean-4.33.1 --receipt valuation-run.json
~~~

The fresh coefficient module is an eventual statement. The onset may depend on the prime, modulus, exponent and target coefficient. The fixed-exponent interpolation calculation in the paper is a written proof, supported by exact floor-ratio controls. The original regular rescaling and conditional point evaluation are kernel-checked against the prepared original environment. No global readable integral-place instance for this ramified order is asserted.

## Rebuilding the manuscript

Run LuaLaTeX three times on the single TeX file in a writable directory with the packages in its preamble. The original Nous logo is embedded. For identical timestamps set SOURCE_DATE_EPOCH=1795694400 and FORCE_SOURCE_DATE=1. Byte-for-byte reproduction also requires the same TeX Live installation and fonts.
