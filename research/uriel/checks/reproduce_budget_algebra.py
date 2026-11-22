"""Reproduce two elementary calculations from the selected-source reading.

Run: python research/uriel/checks/reproduce_budget_algebra.py
Requires SymPy. This does not execute Lean, import proof-archive code, or
verify the arithmetic construction or the Riemann Hypothesis.
"""
from fractions import Fraction
import json
import sympy as sp

n, n_t, n_2, m, k, b, a, x, eps = sp.symbols(
    "n n_t n_2 m k b a x eps", positive=True
)
d_t = n_t / n
d_2 = n_2 / n
bracket = n_t * a * (1 + m**2 / k) + m * (
    2 * n * m * b * x**eps
    + n_2 * k * b * x**eps / (n * (n * x**(-eps)))
)
normalizer = n_t * m * b * d_2 / 2
normalized = (
    2 * a / (m * b * d_2) * (1 + m**2 / k)
    + 4 * m * x**eps / (d_t * d_2)
    + 2 * k * x**(2 * eps) / (d_t * n**2)
)
residual = sp.simplify(bracket / normalizer - normalized)
if residual != 0:
    raise AssertionError(f"Unexpected normalization residual: {residual}")

# Final incompatible bounds in the source's weakened-hypothesis model.
model_x = 100_000
model_err_text = Fraction(model_x) * (1 + Fraction(1, model_x)) + 2
amplified_lower_bound = model_x**10
proposed_weak_upper_bound = model_x**5 * model_err_text
if not amplified_lower_bound > proposed_weak_upper_bound:
    raise AssertionError("Expected the weakened bound to fail.")

print(json.dumps({
    "source_pin": "40e56bab026552e089d7afcfeff08d2defb9c005",
    "sympy_version": sp.__version__,
    "normalization_residual": str(residual),
    "weak_model_x": model_x,
    "weak_model_err_text": str(model_err_text),
    "amplified_lower_bound": str(amplified_lower_bound),
    "proposed_weak_upper_bound": str(proposed_weak_upper_bound),
    "lower_to_upper_ratio_exact": str(
        Fraction(amplified_lower_bound, proposed_weak_upper_bound)
    ),
    "scope": "algebraic rearrangement and final numerical contradiction only",
    "lean_build_or_kernel_replay": False
}, indent=2))

