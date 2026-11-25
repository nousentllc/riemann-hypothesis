import LocalWitnesses
import CoordinateFloor
import FloorTransfer

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Set
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace OriginalFloor

/-- A common positive floor on the punctured neighborhood of the singular
target for the specified original Gram family and its original basis lattice. -/
theorem punctured_floor {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (hM : 3 ≤ M)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M)
      (coordHerm (Fv F v) σ b lam 1) m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 →
        c ≤ (m (hermScal (Fv F v) σ z) (latV b v)).toReal := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := GlobalTheory.T.completion_is_local_ring F v
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have := hlam.1
  obtain ⟨B,e,f,hB,-,he,hf,hfe,-,hcoord⟩ :=
    LocalWitnesses.in_pinned_coordinates σ hσ M J hJ hM d b v
  obtain ⟨e',f',he',hf',hz,hr,hline⟩ := LocalWitnesses.integral_pair v B hB e f he hf (hfe ▸ one_ne_zero)
  let O := (v.adicCompletionIntegers F).toSubring
  have hOo : IsOpen (O : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hOc : IsCompact (O : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have hQ : Continuous (LocalPair.quad B) := by
    exact continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hS : Continuous (fun x => x ⬝ᵥ (B *ᵥ e')) := by
    exact continuous_id.dotProduct continuous_const
  obtain ⟨D,hD,hD0,c,hc,ht⟩ := CoordinateFloor.lower O hOo hOc lam hlam.2
    _ _ hQ hS e' f' he' hf' hz hr hline
  exact ⟨c,hc,FloorTransfer.punctured_of_coordinate_tubes σ hσ M J hJ d b v lam hlam m hm
    _ hQ hcoord D hD hD0 c ht⟩

end OriginalFloor
#print axioms OriginalFloor.punctured_floor
