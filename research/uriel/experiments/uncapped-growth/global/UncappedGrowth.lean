import GermSupport
import OriginalFloor
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open ExceptionalPrimeCriterion Filter
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace UncappedGrowth
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}


/-- Full growth on all positive integer multiples of one fixed N. The original
fiber nonzero assumption at β follows from the local punctured-neighborhood theorem. -/
theorem all_multiples (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (β : F) (hβ : β ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 0 < t →
      c*((N*t:ℕ):ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤
        ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v (N*t))).toReal := by
  have hloc (v : HeightOneSpectrum (𝓞 F)) : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 →
      δ ≤ (m v (hermScal (Fv F v) σ z) (latV b v)).toReal :=
    OriginalFloor.punctured_floor σ hσ M J hJ hM d b v (lam v) (hlam v) (m v) (hm v)
  have hne := fun v => GermSupport.nonzero_at (b := b) hσ hJ hM hlam hm v β hβ (hloc v)
  obtain ⟨N,B,hN,h⟩ := NeighborhoodGrowth.from_punctured_germs (b := b) hσ hJ hM hlam hm β hβ hne
  exact ⟨N,hN,h (fun v _ => hloc v)⟩
end UncappedGrowth
#print axioms UncappedGrowth.all_multiples
