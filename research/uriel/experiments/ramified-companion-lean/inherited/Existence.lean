import Endpoint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped ENNReal TensorProduct
noncomputable section
namespace TargetOne
theorem standard_exists : ∃ lam : Measure K, IsStdV placeTwo lam := by
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  let C : TopologicalSpace.PositiveCompacts K := ⟨⟨O,compact_O⟩, by
    change (interior (O : Set K)).Nonempty
    have ho : IsOpen (O : Set K) := Valued.isOpen_valuationSubring _
    rw [ho.interior_eq]
    exact ⟨0,O.zero_mem⟩⟩
  exact ⟨Measure.addHaarMeasure C,inferInstance,Measure.addHaarMeasure_self⟩
theorem realized (lam : Measure K) (hlam : IsStdV placeTwo lam) :
    ∃ m : H → Measure W, family lam m ∧ m target lattice = (3/4 : ℝ≥0∞) := by
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  obtain ⟨-,hW,hH⟩ := GlobalTheory.T.coordinate_haar_measure ℚ E conjG isCM K 2 gb lam hlam.1
  obtain ⟨m,hm⟩ := GlobalTheory.T.exists_gram_fiber_measures ℚ E conjG isCM 3 J herm_id K locally 1
    (coordW K gb lam 1 3) (coordHerm K conjG gb lam 1) (hW 1 3) (hH 1)
  exact ⟨m,hm,target_one_mass lam hlam m hm⟩
theorem realized_unconditionally : ∃ lam : Measure K, IsStdV placeTwo lam ∧
    ∃ m : H → Measure W, family lam m ∧ m target lattice = (3/4 : ℝ≥0∞) := by
  obtain ⟨lam,hlam⟩ := standard_exists
  exact ⟨lam,hlam,realized lam hlam⟩
end TargetOne
#print axioms TargetOne.realized_unconditionally
