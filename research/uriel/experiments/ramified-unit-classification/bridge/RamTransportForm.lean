import RamTransportFour
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EtaleAwayQuotientEqLocalization

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory Topology
open scoped TensorProduct ENNReal Matrix
noncomputable section
namespace RamTransportForm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (J : Matrix (Fin 3) (Fin 3) E) (b : Module.Basis (Fin 2) F E)
variable (K : Type) [Field K] [Algebra F K] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

abbrev W := Fin 1 → Fin 3 → K ⊗[F] E
abbrev H := HermR K σ 1
abbrev family (lam : Measure K) (m : H σ K → Measure (W (F:=F) (E:=E) K)) :=
  IsGramFib K σ J 1 (coordW K b lam 1 3) (coordHerm K σ b lam 1) m

def coord (X : W (F:=F) (E:=E) K) (p : TargetOne.Idx) :=
  (Algebra.TensorProduct.basis K b).repr (X 0 p.1) p.2

def lattice (O : Set K) : Set (W (F:=F) (E:=E) K) := {X | ∀ p, coord b K X p ∈ O}

omit [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem gram_coordinates (hG : TraceFormGram.trGram σ J b =
    (2 : F) • (1 : Matrix TargetOne.Idx TargetOne.Idx F)) (X : W (F:=F) (E:=E) K) :
    algebraMap F K (1/2) * Algebra.trace K (K ⊗[F] E) (gramR K σ J X 0 0) =
      TargetOne.Q (coord b K X) := by
  have hB : (TraceFormGram.trGram σ J b).map (algebraMap F K) =
      (2:K) • (1 : Matrix TargetOne.Idx TargetOne.Idx K) := by
    rw [hG]
    ext i j
    by_cases h : i=j <;> simp [Matrix.map_apply,Matrix.one_apply,Matrix.smul_apply,h] <;> exact map_ofNat _ _
  let x := X 0
  have htr : Algebra.trace K (K ⊗[F] E) (hR K σ J x x) =
      (fun p : TargetOne.Idx => (Algebra.TensorProduct.basis K b).repr (x p.1) p.2) ⬝ᵥ
        (((2 : K) • (1 : Matrix TargetOne.Idx TargetOne.Idx K)) *ᵥ
          fun p : TargetOne.Idx => (Algebra.TensorProduct.basis K b).repr (x p.1) p.2) := by
    rw [← hB]
    have hh : hR K σ J x x = ∑ i, ∑ j, sigR K σ (x i) * ((1 : K) ⊗ₜ[F] J i j) * x j := rfl
    rw [hh]
    simp only [map_sum,TraceFormGram.trace_entry σ b K,dotProduct,Matrix.mulVec,
      Fintype.sum_prod_type,Matrix.map_apply,TraceFormGram.trGram,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  change _ * Algebra.trace K _ (hR K σ J x x) = _
  rw [htr,one_div,map_inv₀,map_ofNat,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  have ht : (2:K) ≠ 0 := by
    have := (map_ne_zero_iff (algebraMap F K) (RingHom.injective _)).2 (show (2:F)≠0 by norm_num)
    simpa only [map_ofNat] using this
  simp only [smul_eq_mul,←mul_assoc,inv_mul_cancel₀ ht,one_mul,TargetOne.Q,dotProduct,pow_two,coord,x]

omit [MeasurableSpace K] [BorelSpace K] in
theorem lattice_clopen (hCM : IsCMExt F E σ) (hloc : IsLocR K) (O : Set K) (hOc : IsCompact O) (hOo : IsOpen O) :
    IsCompact (lattice b K O) ∧ IsOpen (lattice b K O) := by
  obtain ⟨i1,i2,i3,i4,-⟩ := hloc
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E
    σ hCM K
  let f : K ⊗[F] E → Fin 2 → K := fun y k => (Algebra.TensorProduct.basis K b).repr y k
  let e := (hH 2 b).homeomorph f
  let P : Set (Fin 2 → K) := Set.pi Set.univ fun _ => O
  let B := e ⁻¹' P
  have hBc : IsCompact B := (Homeomorph.isCompact_preimage e).2 (isCompact_univ_pi fun _ => hOc)
  have hBo : IsOpen B := (Homeomorph.isOpen_preimage e).2 (isOpen_set_pi Set.finite_univ fun _ _ => hOo)
  have he : lattice b K O = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B := by
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
theorem original_mass (hCM : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hG : TraceFormGram.trGram σ J b = (2 : F) • (1 : Matrix TargetOne.Idx TargetOne.Idx F))
    (hloc : IsLocR K) (O : Set K) (hOc : IsCompact O) (hOo : IsOpen O)
    (lam : Measure K) (hlam : lam.IsAddHaarMeasure) (m : H σ K → Measure (W (F:=F) (E:=E) K)) (hm : family σ J b K lam m)
    (s : K) (hs : s ≠ 0) (D : ℝ≥0∞) (hD : 0 < D.toReal)
    (ht : ∀ U ∈ 𝓝 s, ∃ V : Set K, MeasurableSet V ∧ V ⊆ U ∧ 0 < (lam V).toReal ∧
      (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K O V) = D * lam V) :
    m (hermScal K σ s) (lattice b K O) = D := by
  classical
  obtain ⟨i1,i2,i3,i4,-⟩ := id hloc
  let := hlam
  obtain ⟨hLc,hLo⟩ := lattice_clopen σ b K hCM hloc O hOc hOo
  obtain ⟨hcm,hpush⟩ := GlobalTheory.T.measurable_coordinate_maps_tensor F E
    σ hCM K 2 b 3 lam hlam
  change Measurable (coord b K) at hcm
  change (coordW K b lam 1 3).map (coord b K) = Measure.pi fun _ => lam at hpush
  let M := m (hermScal K σ s) (lattice b K O)
  have e : M.toReal = D.toReal := by
    by_contra hn
    let ε := |D.toReal-M.toReal|/2
    have hp : 0 < |D.toReal-M.toReal| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hn))
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨U,hU,happrox⟩ := FibreRatio.ratio_field K hloc hCM hJ
      b lam hlam m hm _ hLc hLo s hs ε hε
    obtain ⟨V,hV,hsub,hpos,hfinite⟩ := ht U hU
    have hmV : MeasurableSet (RamTransport.tube K O V) := by
      have hQ : Continuous (TargetOne.Q (R := K)) := by unfold TargetOne.Q; fun_prop
      have hT := (MeasurableSet.iInter fun i : TargetOne.Idx => hOo.measurableSet.preimage
        (measurable_pi_apply (X := fun _ : TargetOne.Idx => K) i)).inter (hV.preimage hQ.measurable)
      convert hT using 1
      ext x; simp [RamTransport.tube]
    have pre : (coord b K) ⁻¹' RamTransport.tube K O V = lattice b K O ∩ {X | algebraMap F K (1/2) *
        Algebra.trace K _ (gramR K σ J X 0 0) ∈ V} := by
      ext X
      change (_ ∧ _ ∈ V) ↔ (_ ∧ _ ∈ V)
      rw [gram_coordinates σ J b K hG]
      rfl
    have hmeas := congrArg (fun μ : Measure (TargetOne.Idx → K) => μ (RamTransport.tube K O V)) hpush
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

theorem family_exists (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hloc : IsLocR K) (lam : Measure K) (hlam : lam.IsAddHaarMeasure) :
    ∃ m : H σ K → Measure (W (F:=F) (E:=E) K), family σ J b K lam m := by
  obtain ⟨i1,i2,i3,i4,-⟩ := id hloc
  obtain ⟨-,hW,hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ
    hCM K 2 b lam hlam
  exact GlobalTheory.T.exists_gram_fiber_measures F E σ hCM
    3 J hJ K hloc 1 (coordW K b lam 1 3)
    (coordHerm K σ b lam 1) (hW 1 3) (hH 1)


/-- The ramified target computation is valid for *any* supplied global Gaussian
presentation having trace-Gram matrix 2I in the specified basis. -/
theorem mass_at_four [Algebra F RamField.K] (hCM : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hG : TraceFormGram.trGram σ J b = (2 : F) • (1 : Matrix TargetOne.Idx TargetOne.Idx F))
    (hn : RamTransportFour.admissibleCount) (lam : Measure RamField.K) (hlam : lam.IsAddHaarMeasure)
    (hvol : lam RamField.integers = 1) (m : H σ RamField.K → Measure (W (F:=F) (E:=E) RamField.K))
    (hm : family σ J b RamField.K lam m) :
    m (hermScal RamField.K σ 4) (lattice b RamField.K RamField.integers) = (257/128:ℝ≥0∞) := by
  let := hlam
  apply original_mass σ J b RamField.K hCM hJ hG RamField.locally _ RamField.integers_compact
    RamField.integers_open lam hlam m hm 4 (by norm_num) (257/128) (by norm_num [ENNReal.toReal_div])
  intro N hN
  obtain ⟨k,hk⟩ := RamField.small_four N hN
  refine ⟨RamField.cylinder (k+5) 4,(RamField.open_cylinder _ _).measurableSet,hk,?_,
    RamTransportFour.tube_four hn lam hvol k⟩
  rw [RamField.cyl_mass lam hvol]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  positivity

theorem realized [Algebra F RamField.K] (hCM : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hG : TraceFormGram.trGram σ J b = (2 : F) • (1 : Matrix TargetOne.Idx TargetOne.Idx F))
    (hn : RamTransportFour.admissibleCount) :
    ∃ lam : Measure RamField.K, lam.IsAddHaarMeasure ∧ lam RamField.integers = 1 ∧
      ∃ m : H σ RamField.K → Measure (W (F:=F) (E:=E) RamField.K), family σ J b RamField.K lam m ∧
        m (hermScal RamField.K σ 4) (lattice b RamField.K RamField.integers) = (257/128 : ℝ≥0∞) := by
  obtain ⟨lam,hl,hvol⟩ := RamField.standard_exists
  obtain ⟨m,hm⟩ := family_exists σ J b RamField.K hCM hJ RamField.locally lam hl
  exact ⟨lam,hl,hvol,m,hm,mass_at_four σ J b hCM hJ hG hn lam hl hvol m hm⟩

end RamTransportForm
#print axioms RamTransportForm.mass_at_four
#print axioms RamTransportForm.realized
