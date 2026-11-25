import Existence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory Topology
open scoped TensorProduct ENNReal Matrix
noncomputable section

namespace RamTransport

variable (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

abbrev W := Fin 1 → Fin 3 → K ⊗[ℚ] TargetOne.E
abbrev H := HermR K TargetOne.conjG 1
abbrev family (lam : Measure K) (m : H K → Measure (W K)) :=
  IsGramFib K TargetOne.conjG TargetOne.J 1 (coordW K TargetOne.gb lam 1 3)
    (coordHerm K TargetOne.conjG TargetOne.gb lam 1) m

def coord (X : W K) (p : TargetOne.Idx) :=
  (Algebra.TensorProduct.basis K TargetOne.gb).repr (X 0 p.1) p.2

def lattice (O : Set K) : Set (W K) := {X | ∀ p, coord K X p ∈ O}

def tube (O C : Set K) : Set (TargetOne.Idx → K) :=
  {x | (∀ i, x i ∈ O) ∧ TargetOne.Q x ∈ C}

omit [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- The same polynomial as the original rank-one trace, after its factor of one half. -/
theorem gram_coordinates (X : W K) :
    algebraMap ℚ K (1/2) * Algebra.trace K (K ⊗[ℚ] TargetOne.E)
      (gramR K TargetOne.conjG TargetOne.J X 0 0) = TargetOne.Q (coord K X) := by
  have htr := TargetOne.trace_coords K (X 0) (X 0)
  change _ * Algebra.trace K _ (hR K _ _ (X 0) (X 0)) = _
  rw [htr,one_div,map_inv₀,map_ofNat,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  have ht : (2:K) ≠ 0 := by
    have := (map_ne_zero_iff (algebraMap ℚ K) (RingHom.injective _)).2 (show (2:ℚ)≠0 by decide)
    simpa only [map_ofNat] using this
  simp only [smul_eq_mul,←mul_assoc,inv_mul_cancel₀ ht,one_mul,TargetOne.Q,dotProduct,pow_two,coord]

omit [MeasurableSpace K] [BorelSpace K] in
theorem lattice_clopen (hloc : IsLocR K) (O : Set K) (hOc : IsCompact O) (hOo : IsOpen O) :
    IsCompact (lattice K O) ∧ IsOpen (lattice K O) := by
  obtain ⟨i1,i2,i3,i4,-⟩ := hloc
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring ℚ TargetOne.E
    TargetOne.conjG TargetOne.isCM K
  let b := TargetOne.gb
  let f : K ⊗[ℚ] TargetOne.E → Fin 2 → K := fun y k => (Algebra.TensorProduct.basis K b).repr y k
  let e := (hH 2 b).homeomorph f
  let P : Set (Fin 2 → K) := Set.pi Set.univ fun _ => O
  let B := e ⁻¹' P
  have hBc : IsCompact B := (Homeomorph.isCompact_preimage e).2 (isCompact_univ_pi fun _ => hOc)
  have hBo : IsOpen B := (Homeomorph.isOpen_preimage e).2 (isOpen_set_pi Set.finite_univ fun _ _ => hOo)
  have he : lattice K O = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B := by
    ext X
    simp only [lattice,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,true_implies,B,P,Set.mem_preimage]
    constructor
    · intro hx a i j
      obtain rfl : a=0 := Subsingleton.elim _ _
      exact hx (i,j)
    · exact fun hx p => hx 0 p.1 p.2
  rw [he]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hBc,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hBo⟩

/-- Cofinal exact ratios determine every original Gram disintegration at a regular
target.  A positive proposed ratio also rules out infinite lattice mass under toReal. -/
theorem original_mass (hloc : IsLocR K) (O : Set K) (hOc : IsCompact O) (hOo : IsOpen O)
    (lam : Measure K) (hlam : lam.IsAddHaarMeasure) (m : H K → Measure (W K)) (hm : family K lam m)
    (s : K) (hs : s ≠ 0) (D : ℝ≥0∞) (hD : 0 < D.toReal)
    (ht : ∀ U ∈ 𝓝 s, ∃ V : Set K, MeasurableSet V ∧ V ⊆ U ∧ 0 < (lam V).toReal ∧
      (Measure.pi fun _ : TargetOne.Idx => lam) (tube K O V) = D * lam V) :
    m (hermScal K TargetOne.conjG s) (lattice K O) = D := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id hloc
  let := hlam
  obtain ⟨hLc,hLo⟩ := lattice_clopen K hloc O hOc hOo
  obtain ⟨hcm,hpush⟩ := GlobalTheory.T.measurable_coordinate_maps_tensor ℚ TargetOne.E
    TargetOne.conjG TargetOne.isCM K 2 TargetOne.gb 3 lam hlam
  change Measurable (coord K) at hcm
  change (coordW K TargetOne.gb lam 1 3).map (coord K) = Measure.pi fun _ => lam at hpush
  let M := m (hermScal K TargetOne.conjG s) (lattice K O)
  have e : M.toReal = D.toReal := by
    by_contra hn
    let ε := |D.toReal-M.toReal|/2
    have hp : 0 < |D.toReal-M.toReal| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hn))
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨U,hU,happrox⟩ := FibreRatio.ratio_field K hloc TargetOne.isCM TargetOne.herm_id
      TargetOne.gb lam hlam m hm _ hLc hLo s hs ε hε
    obtain ⟨V,hV,hsub,hpos,hfinite⟩ := ht U hU
    have hmV : MeasurableSet (tube K O V) := by
      have hQ : Continuous (TargetOne.Q (R := K)) := by unfold TargetOne.Q; fun_prop
      have hT := (MeasurableSet.iInter fun i : TargetOne.Idx => hOo.measurableSet.preimage
        (measurable_pi_apply (X := fun _ : TargetOne.Idx => K) i)).inter (hV.preimage hQ.measurable)
      convert hT using 1
      ext x; simp [tube]
    have pre : (coord K) ⁻¹' tube K O V = lattice K O ∩ {X | algebraMap ℚ K (1/2) *
        Algebra.trace K _ (gramR K TargetOne.conjG TargetOne.J X 0 0) ∈ V} := by
      ext X
      change (_ ∧ _ ∈ V) ↔ (_ ∧ _ ∈ V)
      rw [gram_coordinates]
      rfl
    have hmeas := congrArg (fun μ : Measure (TargetOne.Idx → K) => μ (tube K O V)) hpush
    change (Measure.map _ _) _ = _ at hmeas
    rw [Measure.map_apply hcm hmV,pre] at hmeas
    have ha := happrox V hV hsub
    rw [hmeas,hfinite,ENNReal.toReal_mul] at ha
    change |D.toReal * (lam V).toReal - M.toReal * (lam V).toReal| ≤ ε * (lam V).toReal at ha
    rw [←sub_mul,abs_mul,abs_of_pos hpos] at ha
    have he := (mul_le_mul_iff_left₀ hpos).mp ha
    dsimp [ε] at he
    linarith
  have hM : M ≠ ⊤ := fun he => by rw [he,ENNReal.toReal_top] at e; linarith
  exact (ENNReal.toReal_eq_toReal_iff' hM (ENNReal.toReal_pos_iff.mp hD).2.ne).mp e

theorem family_exists (hloc : IsLocR K) (lam : Measure K) (hlam : lam.IsAddHaarMeasure) :
    ∃ m : H K → Measure (W K), family K lam m := by
  obtain ⟨i1,i2,i3,i4,-⟩ := id hloc
  obtain ⟨-,hW,hH⟩ := GlobalTheory.T.coordinate_haar_measure ℚ TargetOne.E TargetOne.conjG
    TargetOne.isCM K 2 TargetOne.gb lam hlam
  exact GlobalTheory.T.exists_gram_fiber_measures ℚ TargetOne.E TargetOne.conjG TargetOne.isCM
    3 TargetOne.J TargetOne.herm_id K hloc 1 (coordW K TargetOne.gb lam 1 3)
    (coordHerm K TargetOne.conjG TargetOne.gb lam 1) (hW 1 3) (hH 1)

end RamTransport
#print axioms RamTransport.original_mass
#print axioms RamTransport.family_exists
