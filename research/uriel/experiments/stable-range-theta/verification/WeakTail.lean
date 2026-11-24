import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsNe

open MeasureTheory

namespace UrielCheck

def WeakAbsNe : Prop :=
  ∀ (A B C : Type) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC] (H : Set B) (K : Set C), MeasurableSet H → MeasurableSet K → μB H ≠ 0 → μB H ≠ ⊤ →
    μC K ≠ ⊤ → ∀ (f : A × B × C → ℂ) (m : A → C → ℂ) (s c₀ : C → ℂ) (κ : ℂ) (r : ℝ) (w : C → ENNReal), κ ≠ 0 → 0 < r →
    Integrable f (μA.prod (μB.prod μC)) → (∀ x b c, b ∉ H → f (x, b, c) = 0) → (∀ x c, ∀ b ∈ H, f (x, b, c) = s c * m x c) →
    (∀ c, ∫ x, m x c ∂μA = κ * c₀ c) → (∀ c ∈ K, s c = 1 ∧ c₀ c = r) → (∀ c, ‖c₀ c‖ ≤ r ∧ ‖s c‖ₑ ≤ w c) →
    ∫⁻ c in Kᶜ, w c ∂μC ≤ μC K → ∫ y, f y ∂(μA.prod (μB.prod μC)) ≠ 0

/-- The source implication with its last strict inequality weakened to ≤ fails. -/
theorem weak_tail_fails : ¬ WeakAbsNe := by
  classical
  intro claim
  let μ : Measure Unit := Measure.dirac ()
  let ν : Measure Bool := Measure.dirac false + Measure.dirac true
  let K : Set Bool := {false}
  let sign : Bool → ℂ := fun c => if c then -1 else 1
  let f : Unit × Unit × Bool → ℂ := fun p => sign p.2.2
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have product : μ.prod (μ.prod ν) =
      Measure.dirac ((), (), false) + Measure.dirac ((), (), true) := by
    simp only [μ, ν, Measure.prod_add, Measure.dirac_prod_dirac]
  have hf : Integrable f (μ.prod (μ.prod ν)) := by
    rw [product, integrable_add_measure]
    exact ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩
  have int_zero : ∫ p, f p ∂(μ.prod (μ.prod ν)) = 0 := by
    rw [product, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
    simp [f, sign]
  have onK : ν K = 1 := by
    simp [ν, K, Measure.add_apply, Set.indicator]
  have offK : ν Kᶜ = 1 := by
    simp [ν, K, Measure.add_apply, Set.indicator]
  have forced := claim Unit Unit Bool μ μ ν Set.univ K MeasurableSet.univ
    (measurableSet_singleton _) (by simp [μ]) (measure_ne_top _ _)
    (measure_ne_top _ _) f (fun _ _ => 1) sign (fun _ => 1) 1 1 (fun _ => 1)
    one_ne_zero zero_lt_one hf (by simp) (by simp [f])
    (by simp [μ]) (by simp [K, sign])
    (by intro c; cases c <;> simp [sign])
    (by rw [lintegral_const, one_mul, Measure.restrict_apply_univ, offK, onK])
  exact forced int_zero

#print axioms UpperTheory.TP.absNe
#print axioms UrielCheck.weak_tail_fails
end UrielCheck
