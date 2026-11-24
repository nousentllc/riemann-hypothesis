# What was checked in Lean

The proof file AbsNe.lean is byte-identical to the complete file at published commit 40e56bab026552e089d7afcfeff08d2defb9c005. The runner checks its Git blob c04ecf97717ee43cc5c397098c2f425df93548fa and compiles it under its original module name. Its one imported project file, SchurStep.lean, normally brings in a much larger proof environment. For this check we compile a replacement import containing the *exact* definition of UpperTheory.TP.AbsNe from lines 183–189 of the pinned SchurStep.lean. The underlying measure theory comes from the prebuilt pinned Mathlib. The replacement supplies one definition and no new axioms or assumed nonvanishing theorem.

The original file proves nonvanishing for complex-valued product integrals under all the conditions stated in that definition. Its proof compiled unchanged against the reduced environment. WeakTail.lean copies the same definition, renames it, and replaces only the final strict tail inequality with a non-strict one. The replay program checks the literal difference. Lean proves the negation of the resulting universal claim with all of its other hypotheses intact.

The counterexample takes unit point masses on A and B, and a pair of unit atoms on C. The core K contains one atom, the tail contains the other, and H is the entire space B. The sign is +1 on the core and −1 on the tail. All other scalar factors and the envelope are one. The tail mass equals the core mass, and the total integral is zero. This establishes the sharpness of the strict inequality as a uniform sufficient condition under these hypotheses. It says nothing about necessity for an individual nonvanishing theta lift or about what margins are actually attained by the arithmetic data.

Each of the three new compiled objects is separately replayed with Lean's kernel checker. The axiom report for both mathematical theorems lists propext, Classical.choice and Quot.sound. Warnings about deprecated lemma names come from the original proof text. The checks cover the finite counterexample and the abstract noncancellation argument. They do not rebuild the original SchurStep import environment, supply the automorphic hypotheses, or check the full TLiftK or RowSrc theorem.

## Reproduce

Use the Lean 4.33.1 distribution and a built Git checkout of Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. Run the command from this directory after setting the two local paths.

~~~sh
python3 -B replay_lean.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT"
~~~

With a local copy of the published source and its Git tree, also pass the following arguments. The source root contains src/. These checks establish that the published proof file and the original definition at the recorded line range are byte-identical to the checked inputs.

~~~sh
python3 -B replay_lean.py --sdk "$LEAN_SDK" --mathlib "$MATHLIB_CHECKOUT"   --source "$PUBLISHED_SOURCE" --git "$PROOF_CHECKOUT"
~~~

The runner compiles in a fresh temporary directory, checks all three objects with leanchecker, checks both axiom reports, and emits a JSON receipt. The archived receipt was generated with both original-source comparisons enabled. Reproduction needs no API keys or hosted inference.

## The intermediate finite-place selection

TailSelection.lean is a new abstract reconstruction of the step at TPGTail.lean lines 125–140. If the weighted measure of the whole ambient space is finite and the bad sets are measurable, then for any strictly positive threshold and any previously fixed finite set of places S₀, one can enlarge S₀ to S so that the weighted bad mass falls below the threshold. The bad set for S consists of points satisfying all local integral conditions at S while failing some local condition somewhere. Their intersection is empty because every individual place belongs to its own singleton. Continuity from above gives convergence to zero. The theorem establishes existence for this weighted global measure and these inputs. It provides neither the height-integrability estimate supplying finiteness nor the later comparison between Haar measures.

Append --selection-only to the replay command to check this fourth module separately. Its compiler and kernel results are recorded in tail_selection_receipt.json.
