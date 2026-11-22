# Conductor one, odd slot three

Starting point is joint-witness commit `bafda6a` and published source `40e56bab026552e089d7afcfeff08d2defb9c005`. Fix the field $L=\mathbf Q(\zeta_3)$, cutoff $Z=64$ and test weight $e=1$. This is a fixed-cutoff question at the exceptional-set interface. No outer-scale hypothesis is assumed.

## Tests

1. Read both the implementation that produces the centers and the later choices of the cap, field and exceptional set. Check whether any of them specifies a residue modulo 81. Demand the full list for a nonmembership claim unless a uniform argument bypasses the list.
2. Try to produce field-specific witnesses. Investigate the arithmetic input that the class numbers of the $3$-power cyclotomic layers are prime to 3. Test whether the published rank and descent implications convert that input to a zero tower module and allow two genuine first-bound witnesses for this field and the same cutoff. Independent arithmetic evidence and theorems proved locally in Lean must be identified separately. This hypothesis was sharpened during initial source reading, before running its formal or numerical tests.
3. Test whether the center filter for two valid choices can differ on weight 1. Use a boundary value at distance exactly $1/27$ to catch a weak inequality. Any use of supplied centers without an arithmetic justification is only a control.

Positive membership for a reconstructed witness requires a valid bound and a near-center certificate. Identifying the top-level choice further requires equality, uniqueness or a statement uniform over allowed choices. Finite class-number calculations alone cannot certify an infinite tower.
