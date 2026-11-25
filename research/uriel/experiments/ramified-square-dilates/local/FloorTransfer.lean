import LocalTube
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableCoordinateMapsTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Set
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace FloorTransfer

/-- A lower bound on coordinate Haar tubes near zero implies the original
rank-one Gram family has the same lower bound at every nearby nonzero target. -/
theorem punctured_of_coordinate_tubes {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M)
      (coordHerm (Fv F v) σ b lam 1) m)
    (Q : (Fin M × Fin d → Fv F v) → Fv F v) (hQ : Continuous Q)
    (hcoord : ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E,
      algebraMap F (Fv F v) (1/2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
      (gramR (Fv F v) σ J X 0 0) = Q (TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) (X 0)))
    (D : Set (Fv F v)) (hD : IsOpen D) (hD0 : (0:Fv F v) ∈ D) (c : ℝ)
    (hlow : ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ D → c * (lam V).toReal ≤
      ((Measure.pi fun _ : Fin M × Fin d => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ Q x ∈ V}).toReal) :
    ∀ᶠ s : Fv F v in 𝓝 0, s ≠ 0 → c ≤ (m (hermScal (Fv F v) σ s) (latV b v)).toReal := by
  classical
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v) := hloc.1
  have : LocallyCompactSpace (Fv F v) := hloc.2.1
  have : SecondCountableTopology (Fv F v) := hloc.2.2.1
  have : T2Space (Fv F v) := hloc.2.2.2.1
  have := hlam.1
  let O := v.adicCompletionIntegers F
  let coord := fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) (X 0)
  obtain ⟨hcm,hpush⟩ := GlobalTheory.T.measurable_coordinate_maps_tensor F E σ hσ _ d b M lam hlam.1
  change Measurable coord at hcm
  change (coordW (Fv F v) b lam 1 M).map coord = Measure.pi fun _ => lam at hpush
  obtain ⟨hLc,hLo,-⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have hO : IsOpen (O : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  filter_upwards [hD.mem_nhds hD0] with s hs hs0
  apply LocalTube.mass_lower_of_tubes σ hσ M J hJ d b v lam hlam m hm (latV b v) hLc hLo s hs0 c
  intro U hU
  obtain ⟨C, hCc, hCs⟩ := exists_compact_mem_nhds s
  obtain ⟨V, hVsub, hVo, hsV⟩ := mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hU (hD.mem_nhds hs)) hCs)
  have hVD : V ⊆ D := fun x hx => (hVsub hx).1.2
  have hVC : V ⊆ C := fun x hx => (hVsub hx).2
  have hpos := hVo.measure_pos lam ⟨s,hsV⟩
  refine ⟨V,hVo.measurableSet,fun x hx => (hVsub hx).1.1,
    ENNReal.toReal_pos hpos.ne' ((measure_mono hVC).trans_lt hCc.measure_lt_top).ne, ?_⟩
  let T : Set (Fin M × Fin d → Fv F v) := {x | (∀ i, x i ∈ O) ∧ Q x ∈ V}
  have hT : MeasurableSet T := by
    have ht := (MeasurableSet.iInter fun i : Fin M × Fin d => hO.measurableSet.preimage (measurable_pi_apply (X := fun _ : Fin M × Fin d => Fv F v) i)).inter (hVo.measurableSet.preimage hQ.measurable)
    convert ht using 1
    ext x
    simp [T]
  have heq : coord ⁻¹' T = latV b v ∩ {X | algebraMap F (Fv F v) (1/2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V} := by
    ext X
    change ((∀ i, coord X i ∈ O) ∧ Q (coord X) ∈ V) ↔ ((∀ p j k, _ ∈ _) ∧ _ ∈ V)
    rw [hcoord]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨fun p j k => ?_, h'⟩
      obtain rfl : p = 0 := Subsingleton.elim _ _
      exact h (j,k)
    · rintro ⟨h,h'⟩
      exact ⟨fun i => h 0 i.1 i.2,h'⟩
  have heq' := congrArg (fun μ : Measure (Fin M × Fin d → Fv F v) => μ T) hpush
  change (Measure.map coord _) T = _ at heq'
  rw [Measure.map_apply hcm hT, heq] at heq'
  rw [heq']
  exact hlow V hVo.measurableSet hVD

end FloorTransfer
#print axioms FloorTransfer.punctured_of_coordinate_tubes
