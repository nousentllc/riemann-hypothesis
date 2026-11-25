import FourEndpoint
open TargetOne HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct Matrix
noncomputable section
namespace DyadicWave
theorem singular_mass_zero (lam : Measure K) (m : H → Measure W) (hm : family lam m) :
    m (hermScal K conjG 0)=0 := by
  let z := hermScal K conjG 0
  have h := hm.1 z
  have empty :
      (gramR K conjG J ⁻¹' {(z : Matrix (Fin 1) (Fin 1) (K ⊗[ℚ] E))} ∩
       {X : W | IsUnit (gramR K conjG J X).det})=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    obtain ⟨hx,hu⟩ := hX
    change gramR K conjG J X = _ at hx
    change IsUnit (gramR K conjG J X).det at hu
    rw [hx,Matrix.det_fin_one] at hu
    simp [z,hermScal] at hu
  rw [empty,Set.compl_empty] at h
  exact Measure.measure_univ_eq_zero.mp h
end DyadicWave
#print axioms DyadicWave.singular_mass_zero
