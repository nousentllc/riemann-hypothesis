import RamBridge
import RamPlaceCompletion
import RamTransportPlace

open GlobalTheory.CompanionTheory.SW HeckeCharacterZeroLocus.SiegelWeilU MeasureTheory NumberField
open scoped TensorProduct ENNReal
noncomputable section
namespace RamPlaceEndpoint
open RamGlobal (F E conjG gb)
abbrev v := RamFieldPlace.place
abbrev K := v.adicCompletion F
abbrev H := HermR K conjG 1
abbrev W := Fin 1 → Fin 3 → K ⊗[F] E
abbrev fam := RamTransportForm.family conjG RamBridge.J gb K
abbrev atFour := hermScal K conjG 4

/-- The arithmetic place, the original target matrix, and the original
coordinate lattice are all present literally in the formal statement. -/
theorem original (lam : Measure K) (hl : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    m atFour (latV gb v) = (257/128:ℝ≥0∞) :=
  RamTransportPlace.mass_on_latV conjG RamBridge.J gb RamGlobal.isCM RamGlobal.herm_id
    RamGlobal.gram_matrix v RamPlaceCompletion.e RamPlaceCompletion.continuous_e
    RamPlaceCompletion.continuous_e_symm RamPlaceCompletion.integer_preimage RamBridge.normalized lam hl m hm

/-- The tested disintegration exists at this actual global place. -/
theorem realized : ∃ lam : Measure K, IsStdV v lam ∧
    ∃ m : H → Measure W, fam lam m ∧ m atFour (latV gb v) = (257/128:ℝ≥0∞) := by
  letI : BorelSpace K := ⟨rfl⟩
  have hl := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1,i2,i3,i4,-⟩ := id hl
  let g : K ≃ₜ RamField.K := ⟨RamPlaceCompletion.e.toEquiv,
    RamPlaceCompletion.continuous_e,RamPlaceCompletion.continuous_e_symm⟩
  let O : Set K := v.adicCompletionIntegers F
  have hc : IsCompact O := by
    change IsCompact (v.adicCompletionIntegers F : Set K)
    rw [←RamPlaceCompletion.integer_preimage]
    exact (Homeomorph.isCompact_preimage g).2 RamField.integers_compact
  let C : TopologicalSpace.PositiveCompacts K := ⟨⟨O,hc⟩,by
    change (interior O).Nonempty
    have hop : IsOpen O := Valued.isOpen_valuationSubring _
    rw [hop.interior_eq]
    exact ⟨0,(v.adicCompletionIntegers F).zero_mem⟩⟩
  let lam := Measure.addHaarMeasure C
  have hvol : IsStdV v lam := ⟨inferInstance,Measure.addHaarMeasure_self⟩
  obtain ⟨m,hm⟩ := RamTransportForm.family_exists conjG RamBridge.J gb K RamGlobal.isCM
    RamGlobal.herm_id hl lam hvol.1
  exact ⟨lam,hvol,m,hm,original lam hvol m hm⟩

end RamPlaceEndpoint
#print axioms RamPlaceEndpoint.original
#print axioms RamPlaceEndpoint.realized
