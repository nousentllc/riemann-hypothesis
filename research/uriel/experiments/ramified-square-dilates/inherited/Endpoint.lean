import GaussianTrace
import Nearby
import Tubes
import Neighborhoods
import Shallow
import DyadicLocal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace TargetOne
abbrev W := Fin 1 → Fin 3 → K ⊗[ℚ] E
abbrev H := HermR K conjG 1
abbrev J := (1 : Matrix (Fin 3) (Fin 3) E)
abbrev lattice : Set W := latV gb placeTwo
abbrev target : H := hermScal K conjG 1
abbrev family (lam : Measure K) (m : H → Measure W) :=
  IsGramFib K conjG J 1 (coordW K gb lam 1 3) (coordHerm K conjG gb lam 1) m
theorem compact_O : IsCompact (O : Set K) := by
  haveI : CompactSpace O := ei.toHomeomorph.compactSpace
  exact isCompact_iff_compactSpace.2 inferInstance
theorem lattice_clopen : IsCompact lattice ∧ IsOpen lattice := by
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring ℚ E conjG isCM K
  let f : K ⊗[ℚ] E → Fin 2 → K := fun y k => (Algebra.TensorProduct.basis K gb).repr y k
  let e := (hH 2 gb).homeomorph f
  let P : Set (Fin 2 → K) := Set.pi Set.univ fun _ => (O : Set K)
  let B := e ⁻¹' P
  have hBc : IsCompact B := (Homeomorph.isCompact_preimage e).2 (isCompact_univ_pi fun _ => compact_O)
  have hBo : IsOpen B := (Homeomorph.isOpen_preimage e).2
    (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _)
  have he : lattice = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B := by
    ext Y
    simp only [lattice,latV, Set.mem_setOf_eq, Set.mem_pi,Set.mem_univ,true_implies,B,P,Set.mem_preimage]
    rfl
  rw [he]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hBc,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hBo⟩
theorem half_coord (x : Idx → K) :
    (2:K)⁻¹*(x ⬝ᵥ (((2:K) • (1 : Matrix Idx Idx K)) *ᵥ x)) = Q x := by
  have ht : (2:K) ≠ 0 := by
    have h := (map_ne_zero_iff (algebraMap ℚ K) (RingHom.injective _)).2 (show (2:ℚ) ≠ 0 by decide)
    simpa only [map_ofNat] using h
  rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,←mul_assoc,inv_mul_cancel₀ ht,one_mul,Q,dotProduct,pow_two]
theorem target_one (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) : (m target lattice).toReal = 3/4 := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := locally
  haveI := hlam.1
  have hU : IsOpen ({0}ᶜ : Set K) := isOpen_compl_singleton
  have hs : (1:K) ∈ ({0}ᶜ : Set K) := one_ne_zero
  have h := local_mass_from_tests conjG isCM 3 J herm_id 2 gb placeTwo
    ((2:K) • (1 : Matrix Idx Idx K)) (trace_coords K) lam hlam m hm 1 (3/4)
    {0}ᶜ hU hs (fun _ hz => hz) locally lattice_clopen.1 lattice_clopen.2
  apply (show _ → (m target lattice).toReal = 3/4 from fun hD => by simpa using h hD)
  intro N hN
  obtain ⟨k,hc⟩ := small_cylinder _ (Filter.inter_mem (hU.mem_nhds hs) hN)
  refine ⟨cylinder (k+3) 1,compact_cylinder _ _,hc,?_,?_⟩
  · rw [Measure.real,cyl_mass lam hlam.2,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
    positivity
  · simp only [half_coord]
    change (Measure.pi fun _ : Idx => lam) (tube (k+3) 1) = _
    simpa using tube_three_quarters lam hlam.2 k
theorem target_one_mass (lam : Measure K) (hlam : IsStdV placeTwo lam)
    (m : H → Measure W) (hm : family lam m) : m target lattice = (3/4 : ℝ≥0∞) := by
  have h := target_one lam hlam m hm
  have hfin : m target lattice ≠ ⊤ := by intro ht; rw [ht,ENNReal.toReal_top] at h; norm_num at h
  apply ENNReal.toReal_eq_toReal_iff' hfin (by finiteness) |>.mp
  simpa using h
end TargetOne
#print axioms TargetOne.target_one_mass
