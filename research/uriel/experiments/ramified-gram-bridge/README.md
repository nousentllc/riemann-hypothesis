# A ramified Gram fiber at target four

[Paper](Ramified_Gram_Fiber.pdf) · [Editable LuaLaTeX](Ramified_Gram_Fiber.tex) · [Download the full ZIP from GitHub](https://github.com/nousentllc/riemann-hypothesis/raw/refs/heads/experiments/uriel-ramified-lean-bridge/research/uriel/experiments/ramified-gram-bridge/Nous_Ramified_Gram_Fiber_Package.zip)

Lean proves that the original regular Gram-fiber measure of the original coordinate lattice at target four is **257/128**. The base field is ℚ(√2), the CM field is ℚ(√2, i), the form is the three-dimensional identity, and the place is the unique prime above two. The result holds for every normalized additive Haar measure and every admissible original Gram family. A second theorem supplies such a Haar measure and family. [Named-place equality and existence](bridge/RamPlaceEndpoint.lean)

## Why the five-digit result matters

At five uniformizer digits the primitive contribution is 15/8 and the all-divisible contribution is 1/8. The total is two. At six digits the primitive contribution stays at 15/8 and the all-divisible part rises to 17/128. The unit-square lifting argument propagates a certified finite census through every cofinal depth. The original rank-one regular-fiber formula identifies that ratio with the assigned measure at four. The formal proof constructs the comparison with the named prime and proves it carries the original integral lattice to the one counted. [Pivot permutation](bridge/RamBasePivot.lean) · [All-depth counting](bridge/RamLift.lean) · [Integral sets in the actual completion](bridge/RamPlaceCompletion.lean)

At modulus 32, which is uniformizer depth ten, Lean counts **2,260,595,906,707,456** ordered six-tuples out of 2⁶⁰. The density denominator is 2⁵⁰. The finite split and the independent additive-character calculation explain the excess over two. [Finite count](bridge/RamBase.lean) · [Divisibility split](bridge/RamBaseSplit.lean) · [Character calculation](bridge/characters.json)

## Verification

All 81 study modules, including 27 new bridge modules, passed Lean compilation and the separate kernel checker. Adding one to the claimed numerator caused Lean to reject the equality. Both named-place declarations report only Classical.choice, Quot.sound and propext. The selected original-import replay accepted and located 29,109 of 29,137 considered records over the pinned Mathlib base. The replay skips 28 unsafe or partial records. This is a local measure theorem; a full rebuild of the original RH archive was outside this run. [Study receipt](verification/receipt.json) · [Original replay](verification/import_replay.txt) · [Proof-term dependency checks](verification/ramified_dependencies.txt)

For an offline check of the numerical data, source hashes and saved receipts, run this from the extracted study directory.

~~~sh
python3 -B verify.py
~~~

For a fresh formal run use the Lean 4.33.1 SDK at commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, a built Mathlib checkout at 0df444a360eaa60ab8c11dca51a86af692955474, and the src directory of original project revision 40e56bab026552e089d7afcfeff08d2defb9c005. Set LEAN_SDK, MATHLIB_CHECKOUT, PINNED_SRC and STUDY_CACHE to those local paths and a cache directory, respectively. The first command restores the selected, hash-pinned original proof objects from their public archives. The study sources and inventories are included in the ZIP.

~~~sh
python3 -B restore_cache.py --sdk "$LEAN_SDK" --destination "$STUDY_CACHE"
python3 -B verification/check_imports.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj"
python3 -B verification/replay.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT" --objects "$STUDY_CACHE/obj" --original "$PINNED_SRC" --jobs 3
~~~

The paper embeds its original Nous PNG. Run LuaLaTeX three times on Ramified_Gram_Fiber.tex in a writable directory. The release uses TeX Live 2026 with SOURCE_DATE_EPOCH=1795582800 and FORCE_SOURCE_DATE=1. The ZIP includes its PDF, that one TeX source, all study files and SHA256SUMS. [Paper checks](verification/paper.json) · [Earlier written study](https://github.com/nousentllc/riemann-hypothesis/tree/b040ed9063835e90efdecd1e4350ed35708317c0/research/uriel/experiments/uncapped-growth)

Justin Candler selected the question and research design. Uriel and three AI proof workers developed and tested the formal arguments. The original formalization, Mathlib, and prior local-density methods are credited in the paper.
