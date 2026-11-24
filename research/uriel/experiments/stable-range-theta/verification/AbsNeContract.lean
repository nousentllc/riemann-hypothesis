import Mathlib

open MeasureTheory

namespace UpperTheory.TP
def AbsNe : Prop :=
  ∀ (A B C : Type) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC] (H : Set B) (K : Set C), MeasurableSet H → MeasurableSet K → μB H ≠ 0 → μB H ≠ ⊤ →
    μC K ≠ ⊤ → ∀ (f : A × B × C → ℂ) (m : A → C → ℂ) (s c₀ : C → ℂ) (κ : ℂ) (r : ℝ) (w : C → ENNReal), κ ≠ 0 → 0 < r →
    Integrable f (μA.prod (μB.prod μC)) → (∀ x b c, b ∉ H → f (x, b, c) = 0) → (∀ x c, ∀ b ∈ H, f (x, b, c) = s c * m x c) →
    (∀ c, ∫ x, m x c ∂μA = κ * c₀ c) → (∀ c ∈ K, s c = 1 ∧ c₀ c = r) → (∀ c, ‖c₀ c‖ ≤ r ∧ ‖s c‖ₑ ≤ w c) →
    ∫⁻ c in Kᶜ, w c ∂μC < μC K → ∫ y, f y ∂(μA.prod (μB.prod μC)) ≠ 0

end UpperTheory.TP
