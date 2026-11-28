# Lower certificates on the 64-cycle

From this directory run `python3 check.py --check`. Python's standard library and a C++17 compiler named `c++` suffice. The driver recomputes the analytic floor, validates the mark table with rational enclosures, compiles the optimizer in a temporary directory, reruns the four integer threshold searches, checks literal witnesses in physical coordinates, and compares the resulting JSON with `results.json`. Omitting `--check` regenerates that file. The exact affine and threshold conventions are in the lower chapter of the manuscript.

A width-16 order first recursively visits the child containing the minimum. The recursion generates all width-16 orders by looping over the two canonical child orders, then over the two physical child parities. Indices are zero-based in this complete list. For a dense quarter normalize coordinate entries at ranks 0 and 8 to 0 and 1. For sparse quarter D, normalize only its rank 0 to 0 after fixing the parent center and the first D site. The sparse step is an odd integer modulo 16.

## Results fields

- `single_pass` and `either_pass` count sparse chart pairs reaching the stated threshold for all dense completions. Their denominator is 16,384.
- `passing_best_uses_new_D_mask` counts selected maximizers with a positive certificate and a D mask outside the previous eleven masks. This includes equality at the threshold. Mask bit indices are canonical ranks inside D.
- An integer margin is the denominator of the target times the recovered mass in eighths, less its numerator times exposure in eighths. The two omitted nonnegative parent credits are recorded separately in the literal replay. A negative lower margin has no global upper-bound meaning.
- Each row of `full_dense_cross_on_coarse_misses` is [D order, odd step, passing dense pairs, distinct unresolved A orders, distinct unresolved B orders, first unresolved A, first unresolved B]. Its per-row denominator is 65,536. This adaptive cross is evaluated at 10.12%. Identical dense payoff curves are weighted by multiplicity.
- `frozen_crosswalk` independently identifies the historical exceptional sixteen-coordinate D list. Together with the ordinary frozen baseline it leaves 768 normalized chart tuples without a 10.12% certificate from the two menus. Every such tuple still has the frozen lower guarantee.
- Each `wider_residual` row is [odd step, detailed C orders, passing C orders, smallest margin, largest margin]. It evaluates the unresolved D and B orders and retains a universal lower envelope over A. On D it tests all compatible masks with at most nine leaves. On C it tests those with at most eight. Active rates are 19/8 except at each quarter's minimum, where all positive rates in eighths up to 19/8 are tested independently. This is an additional restricted test with exact coordinates in the sparse half. Dense-parent and global-root credits stay zero in the lower objective.

## Scope and chronology

The initial design in `DESIGN.md` preceded the support search. The second sparse anchor, full dense cross, more detailed sparse support test, and literal-window-prefactor improvement were follow-ups to the initial results. The source score's sufficiency is a mathematical transport argument for sufficiently late scales. The computer checks finite chart operations, numerical inequalities by exact enclosures, and source parameters used in that argument. It does not construct a particular arithmetic host or identify the retained set chosen in Lean.
