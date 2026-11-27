import RamTransportForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory Topology
open NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
noncomputable section
namespace RamTransportPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- Transfers the calculation onto the pinned library's exact `latV` type.
The hypotheses expose which integral subring a topological ring isomorphism must preserve. -/
theorem mass_on_latV (σ : E →ₐ[F] E) (J : Matrix (Fin 3) (Fin 3) E)
    (b : Module.Basis (Fin 2) F E) (hCM : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hG : TraceFormGram.trGram σ J b = (2 : F) • (1 : Matrix TargetOne.Idx TargetOne.Idx F))
    (v : HeightOneSpectrum (𝓞 F)) (e : Fv F v ≃+* RamField.K)
    (he : Continuous e) (hei : Continuous e.symm)
    (hO : e ⁻¹' RamField.integers = (v.adicCompletionIntegers F : Set (Fv F v)))
    (hn : RamTransportFour.admissibleCount) (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 3 → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 3) (coordHerm (Fv F v) σ b lam 1) m) :
    m (hermScal (Fv F v) σ 4) (latV b v) = (257/128:ℝ≥0∞) := by
  classical
  let K' := Fv F v
  let O' : Set K' := v.adicCompletionIntegers F
  letI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hl := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1,i2,i3,i4,-⟩ := id hl
  let := hlam.1
  let g : Fv F v ≃ₜ RamField.K := ⟨e.toEquiv,he,hei⟩
  let μ : Measure RamField.K := lam.map e
  have hμ : μ.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map lam he hei
  let := hμ
  have hv : μ RamField.integers = 1 := by
    rw [show μ = lam.map e from rfl,Measure.map_apply he.measurable RamField.integers_open.measurableSet,hO,hlam.2]
  have hcompact : IsCompact O' := by
    change IsCompact (v.adicCompletionIntegers F : Set (Fv F v))
    rw [←hO]
    exact (Homeomorph.isCompact_preimage g).2 RamField.integers_compact
  have hopen : IsOpen O' := Valued.isOpen_valuationSubring _
  have latIdent : latV (M:=3) (n:=1) b v = RamTransportForm.lattice b (Fv F v) O' := by
    ext X
    constructor
    · intro hx p; exact hx 0 p.1 p.2
    · intro hx a i j
      obtain rfl : a=0 := Subsingleton.elim _ _
      exact hx (i,j)
  rw [latIdent]
  have hs : (4:Fv F v) ≠ 0 := by
    intro ha
    have hh := congrArg e ha
    simpa only [map_ofNat,map_zero] using (show e 4 ≠ 0 by rw [map_ofNat]; norm_num) (hh.trans (map_zero e))
  apply RamTransportForm.original_mass σ J b (Fv F v) hCM hJ hG hl O' hcompact hopen lam hlam.1 m hm
    4 hs (257/128) (by norm_num [ENNReal.toReal_div])
  intro U hU
  have hNU : e.symm ⁻¹' U ∈ 𝓝 (4:RamField.K) := by
    apply hei.continuousAt
    simpa only [map_ofNat] using hU
  obtain ⟨k,hsub⟩ := RamField.small_four _ hNU
  let C := RamField.cylinder (k+5) 4
  have hc : MeasurableSet C := (RamField.open_cylinder _ _).measurableSet
  have measured : μ C = lam (e ⁻¹' C) := Measure.map_apply he.measurable hc
  refine ⟨e ⁻¹' C,he.measurable hc,fun x hx => ?_,?_,?_⟩
  · simpa only [Set.mem_preimage,RingEquiv.symm_apply_apply] using hsub hx
  · rw [←measured,RamField.cyl_mass μ hv]
    simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
    positivity
  · let φ (x : TargetOne.Idx → Fv F v) := fun i => e (x i)
    have hp : MeasurePreserving φ (Measure.pi fun _ => lam) (Measure.pi fun _ => μ) :=
      measurePreserving_pi _ _ (fun _ => (show MeasurePreserving e lam μ from ⟨he.measurable,rfl⟩))
    have hT : MeasurableSet (RamTransport.tube RamField.K RamField.integers C) := by
      have hQ : Continuous (TargetOne.Q (R := RamField.K)) := by unfold TargetOne.Q; fun_prop
      have hT := (MeasurableSet.iInter fun i : TargetOne.Idx => RamField.integers_open.measurableSet.preimage
        (measurable_pi_apply (X := fun _ : TargetOne.Idx => RamField.K) i)).inter (hc.preimage hQ.measurable)
      convert hT using 1
      ext x; simp [RamTransport.tube]
    have pre : φ ⁻¹' RamTransport.tube RamField.K RamField.integers C =
        RamTransport.tube (Fv F v) O' (e ⁻¹' C) := by
      ext x
      have hpol : e (TargetOne.Q x) = TargetOne.Q (φ x) := by simp only [TargetOne.Q,map_sum,map_pow,φ]
      change ((∀ i, e (x i) ∈ RamField.integers) ∧ TargetOne.Q (φ x) ∈ C) ↔
        ((∀ i, x i ∈ O') ∧ e (TargetOne.Q x) ∈ C)
      rw [hpol]
      have hmem (z : Fv F v) : e z ∈ RamField.integers ↔ z ∈ O' :=
        Set.ext_iff.mp hO z
      simp only [hmem]
    rw [←pre,hp.measure_preimage hT.nullMeasurableSet,←measured]
    exact RamTransportFour.tube_four hn μ hv k

end RamTransportPlace
#print axioms RamTransportPlace.mass_on_latV
