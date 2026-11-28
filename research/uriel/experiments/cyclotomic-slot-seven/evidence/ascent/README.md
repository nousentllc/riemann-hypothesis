# Seven-primary class ascent

The six Lean files in this directory generalize the previous cubic class-field induction, then instantiate it on the actual seven-power layers Fn. Seven.Ascent.singlePlaceAscent takes an arbitrary prime p, a totally complex F, a Galois extension E/F of degree p, and a finite place outside which E/F is unramified. If p does not divide the class number of F, it does not divide that of E. Seven.Ascent.allCyclotomicLayers instantiates the result on each positive original tower layer with the concrete field CyclotomicField 7 ℚ at the bottom. Its class-number seed comes from the separate seven-base unit. All 39 new declarations printed in these six modules use only propext, Classical.choice and Quot.sound.

## Reproduce

Python's standard library suffices to run the finite controls.

```sh
python3 -B control.py > /tmp/seven-group.json
diff -u results.json /tmp/seven-group.json
```

For the scoped proof, use the Lean 4.33.1 SDK, a built Mathlib checkout at 0df444a360eaa60ab8c11dca51a86af692955474, and the original project checkout at 40e56bab026552e089d7afcfeff08d2defb9c005. The source parameter names the root containing src/.

```sh
python3 -B replay.py --source "$ORIGINAL" --mathlib "$MATHLIB" --toolchain "$SDK" --objects "$PROJECT_OBJECTS"
```

Each cached original object must match its recorded SHA-256; missing objects are rebuilt from source checked against its original Git blob ID. The recorded warm run checked all 342 transitive original modules, compiled the six local Lean modules, the neighboring SevenBase and the earlier generic HilbertNormal and SemilinearTransport modules from their specified sources, then replayed all nine research modules with leanchecker. Neither this unit nor its finite controls rebuild the full RH proof. The original project and prior-term anchors, code provenance, and verbatim text of the two older research imports are supplied. Machine version text and which original objects must be rebuilt can differ at replay.

## Controls and scope

The group of 343 upper unitriangular matrices over F7 has 57 cyclic order-seven subgroups. Each lies in an index-seven normal subgroup. The 56 noncentral lines each belong to one maximal normal subgroup, and the central line to all eight. Two independent inertia directions together generate all 343 elements. In S3 a single transposition has three conjugates with normal closure all of S3. These check which finite-group assumptions matter. They do not identify a class field or an actual inertia group of a named cyclotomic extension.

The topology of the cyclotomic fields and the existence arguments in class field theory are kernel-checked. The proof does not calculate higher class numbers, choose unit systems, or give numerical exceptional centers. The written field theorem is a prime-degree instance of the classical one-ramified-prime criterion; the contribution here is the source-typed Lean proof and its use on the seven-primary slot.
