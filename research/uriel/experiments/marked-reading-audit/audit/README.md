# Verification boundaries

The preregistered scorer lives in `pilot/`. Three separate checks address questions its output alone cannot settle.

* `circuits/check.py` reconstructs the electrical calibration by a two-root forest calculation and compares exact rational voltages and currents to the nodal solution. It checks the four evidence sets and their labels in each layout.
* `audit/displays.py` reads the saved prompts without importing the renderer. It reconstructs the exact oracle and all 72 request digests, compares the three printed displays, and tests four intentionally corrupted inputs. A single misplaced star must fail even if exactly two stars remain.
* `audit/crosscheck.py post` reads completed answers from their visible JSON text, and independently scores all 72 arms and records. It checks the individual certificates against the official case table, reconstructs the family comparisons, and compares the signs and missing-outcome bounds with the released results. The local timing report uses client-observed start and finish times. Server metrics and wall times have different meanings.

The missing-response bounds follow from monotonicity. A family with an observed failed reply cannot be completed by filling in the other reply. A family with only passes and missing replies can be. For the largest possible difference in complete families, assign all missing left-arm outcomes to pass and all missing right-arm outcomes to fail. Reverse those assignments for the smallest difference. These extremes are jointly attainable because each missing session has its own outcome. The reference implementation checks every possible pattern of observed passes, failures, and missing values in a pair of two-reply families (81 patterns). Missing-as-failure remains the primary analysis.

The response archive contains the terminal text and usage metadata for each session. Replaying a score re-evaluates the archived response. Running the model again would create a different experiment. The paper is an account of six purpose-built circuits and the specified reader; its error frequencies cannot serve as an audit of Lean or of a model's internal reasoning.
