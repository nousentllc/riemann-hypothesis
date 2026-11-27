import CompanionEndpoint
import UnitCells
import RamFieldRamification

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory Topology
open NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix algebraMap
noncomputable section
namespace UnitTransport
open RamGlobal (F E conjG gb)
open RamPlaceEndpoint (v K H W fam)
open CompanionTransport (IntegralUnits)
open RamDilate.UnitClass (bit)

abbrev UnitMass := RamDilate.UnitClass.mass

private theorem liftUnit (u : IntegralUnits) :
    ∃ w : RamField.Oˣ, RamField.inc (w:RamField.O) =
      RamPlaceCompletion.e ((u : v.adicCompletionIntegers F) : K) := by
  let e := RamPlaceCompletion.e
  have image (z : v.adicCompletionIntegers F) : e (z:K) ∈ RamField.integers :=
    (Set.ext_iff.mp RamPlaceCompletion.integer_preimage _).2 z.property
  obtain ⟨x,hx⟩ := image u
  obtain ⟨y,hy⟩ := image (↑u⁻¹)
  have hxy : x*y=1 := by
    apply RamField.inc_injective
    rw [map_mul,hx,hy,←map_mul,map_one]
    have hv := congrArg (fun t : v.adicCompletionIntegers F => (t:K)) u.val_inv
    change ((u : v.adicCompletionIntegers F) : K) * ((↑u⁻¹ : v.adicCompletionIntegers F) : K) = 1 at hv
    rw [hv,map_one]
  exact ⟨⟨x,y,hxy,mul_comm x y ▸ hxy⟩,hx⟩


/-- The model image of the original unit. Its value is fixed by the completion equivalence. -/
noncomputable def modelUnit (u : IntegralUnits) : RamField.Oˣ := (liftUnit u).choose

theorem modelUnit_value (u : IntegralUnits) : RamField.inc (modelUnit u : RamField.O) =
    RamPlaceCompletion.e ((u : v.adicCompletionIntegers F) : K) := (liftUnit u).choose_spec

def classBit (u : IntegralUnits) : Bool := bit (modelUnit u)

/-- The full unit-residue classification on the original lattice, for every admissible
normalized Haar measure and disintegrating fiber family. -/
theorem original (k : ℕ) (hk : 1≤k) (u : IntegralUnits)
    (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    m (hermScal K conjG ((4:K)^k * ((u : v.adicCompletionIntegers F) : K))) (latV gb v) =
      UnitMass k (classBit u) := by
  classical
  let e := RamPlaceCompletion.e
  have he := RamPlaceCompletion.continuous_e
  have hei := RamPlaceCompletion.continuous_e_symm
  have hO := RamPlaceCompletion.integer_preimage
  let O' : Set K := v.adicCompletionIntegers F
  let : BorelSpace K := ⟨rfl⟩
  have hl := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1,i2,i3,i4,-⟩ := id hl
  let := hlam.1
  let g : K ≃ₜ RamField.K := ⟨e.toEquiv,he,hei⟩
  let μ : Measure RamField.K := lam.map e
  have hμ : μ.IsAddHaarMeasure := e.toAddEquiv.isAddHaarMeasure_map lam he hei
  let := hμ
  have hv : μ RamField.integers = 1 := by
    rw [show μ = lam.map e from rfl,Measure.map_apply he.measurable RamField.integers_open.measurableSet,hO,hlam.2]
  have hcompact : IsCompact O' := by
    change IsCompact (v.adicCompletionIntegers F : Set K)
    rw [←hO]
    exact (Homeomorph.isCompact_preimage g).2 RamField.integers_compact
  have hopen : IsOpen O' := Valued.isOpen_valuationSubring _
  have latIdent : latV (M:=3) (n:=1) gb v = RamTransportForm.lattice gb K O' := by
    ext X
    constructor
    · intro hx p; exact hx 0 p.1 p.2
    · intro hx a i j
      obtain rfl : a=0 := Subsingleton.elim _ _
      exact hx (i,j)
  rw [latIdent]
  let s : K := 4^k * ((u : v.adicCompletionIntegers F) : K)
  let w := modelUnit u
  let a : RamField.O := (4:RamField.O)^k * (w:RamField.O)
  have hw : RamField.inc (w:RamField.O) = e ((u : v.adicCompletionIntegers F) : K) := modelUnit_value u
  have es : e s = RamField.inc a := by
    simp only [s,a,map_mul,map_pow,map_ofNat,hw]
  have hs : s ≠ 0 := by
    have h4 : (4:K) ≠ 0 := by norm_num
    exact mul_ne_zero (pow_ne_zero _ h4)
      (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).ne_zero
  apply RamTransportForm.original_mass conjG RamBridge.J gb K RamGlobal.isCM RamGlobal.herm_id
    RamGlobal.gram_matrix hl O' hcompact hopen lam hlam.1 m hm s hs
      (UnitMass k (classBit u)) (RamDilate.UnitClass.mass_positive k hk _)
  intro U hU
  have hNU : e.symm ⁻¹' U ∈ 𝓝 (RamField.inc a) := by
    apply hei.continuousAt
    rw [←es,e.symm_apply_apply]
    exact hU
  let r0 := 2*k+1
  obtain ⟨n,hsub⟩ := DilateTransport.small a r0 _ hNU
  let r := n+r0
  let C := RamField.cylinder r (RamField.digit r a)
  have hcC : MeasurableSet C := (RamField.open_cylinder _ _).measurableSet
  have measured : μ C = lam (e ⁻¹' C) := Measure.map_apply he.measurable hcC
  refine ⟨e ⁻¹' C,he.measurable hcC,fun x hx => ?_,?_,?_⟩
  · simpa only [Set.mem_preimage,RingEquiv.symm_apply_apply] using hsub hx
  · rw [←measured,RamField.cyl_mass μ hv]
    simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
    positivity
  · let φ (x : TargetOne.Idx → K) := fun i => e (x i)
    have hp : MeasurePreserving φ (Measure.pi fun _ => lam) (Measure.pi fun _ => μ) :=
      measurePreserving_pi _ _ (fun _ => (show MeasurePreserving e lam μ from ⟨he.measurable,rfl⟩))
    have hT : MeasurableSet (RamTransport.tube RamField.K RamField.integers C) := by
      have hQ : Continuous (TargetOne.Q (R := RamField.K)) := by unfold TargetOne.Q; fun_prop
      have ht := (MeasurableSet.iInter fun i : TargetOne.Idx => RamField.integers_open.measurableSet.preimage
        (measurable_pi_apply (X := fun _ : TargetOne.Idx => RamField.K) i)).inter (hcC.preimage hQ.measurable)
      convert ht using 1
      ext x; simp [RamTransport.tube]
    have pre : φ ⁻¹' RamTransport.tube RamField.K RamField.integers C =
        RamTransport.tube K O' (e ⁻¹' C) := by
      ext x
      have hpol : e (TargetOne.Q x) = TargetOne.Q (φ x) := by simp only [TargetOne.Q,map_sum,map_pow,φ]
      change ((∀ i, e (x i) ∈ RamField.integers) ∧ TargetOne.Q (φ x) ∈ C) ↔
        ((∀ i, x i ∈ O') ∧ e (TargetOne.Q x) ∈ C)
      rw [hpol]
      have hmem (z : K) : e z ∈ RamField.integers ↔ z ∈ O' := Set.ext_iff.mp hO z
      simp only [hmem]
    rw [←pre,hp.measure_preimage hT.nullMeasurableSet,←measured]
    have ht := RamDilate.UnitClass.all_late k (2*r) hk (by dsimp [r,r0]; omega) w μ hv
    dsimp only at ht
    rw [RamDilate.StableOdd.even_cell] at ht
    exact ht


private def placeOrderMap : RamField.O →+* v.adicCompletionIntegers F where
  toFun a := ⟨RamPlaceCompletion.e.symm (RamField.inc a),
    (Set.ext_iff.mp RamPlaceCompletion.integer_preimage _).1 (by
      change RamPlaceCompletion.e (RamPlaceCompletion.e.symm (RamField.inc a)) ∈ RamField.integers
      rw [RingEquiv.apply_symm_apply]
      exact ⟨a,rfl⟩)⟩
  map_one' := by apply Subtype.ext; exact (map_one (RamPlaceCompletion.e.symm.toRingHom.comp RamField.inc))
  map_zero' := by apply Subtype.ext; exact (map_zero (RamPlaceCompletion.e.symm.toRingHom.comp RamField.inc))
  map_add' a b := by apply Subtype.ext; exact (map_add (RamPlaceCompletion.e.symm.toRingHom.comp RamField.inc) a b)
  map_mul' a b := by apply Subtype.ext; exact (map_mul (RamPlaceCompletion.e.symm.toRingHom.comp RamField.inc) a b)

private theorem model_roundtrip (w : RamField.Oˣ) :
    modelUnit (Units.map placeOrderMap.toMonoidHom w) = w := by
  apply Units.ext
  apply RamField.inc_injective
  rw [modelUnit_value]
  exact RamPlaceCompletion.e.apply_symm_apply _

private theorem val_unit (u : IntegralUnits) : Valued.v ((u : v.adicCompletionIntegers F) : K)=1 :=
  (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K:=F) (v:=v)).mp u.isUnit

/-- Unit scaling ranges over precisely the original valuation shell of the scalar 4^k. -/
theorem valuation_shell (k : ℕ) (s : K) :
    Valued.v s = Valued.v ((4:K)^k) ↔ ∃ u : IntegralUnits,
      s=(4:K)^k*((u:v.adicCompletionIntegers F):K) := by
  constructor
  · intro h
    have h4 : ((4:K)^k) ≠ 0 := pow_ne_zero _ (by norm_num)
    let z := s/(4:K)^k
    have hz : Valued.v z=1 := by
      dsimp only [z]
      rw [map_div₀,h,div_self ((Valuation.ne_zero_iff _).mpr h4)]
    let a : v.adicCompletionIntegers F := ⟨z,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_of_eq hz)⟩
    have hu : IsUnit a :=
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K:=F) (v:=v)).mpr hz
    refine ⟨hu.unit,?_⟩
    rw [IsUnit.unit_spec]
    change s = (4:K)^k*(s/(4:K)^k)
    field_simp
  · rintro ⟨u,rfl⟩
    rw [map_mul,val_unit,mul_one]

/-- The multiplicative value used for this shell has normalized additive exponent 4k. -/
theorem valuation_exponent (k : ℕ) :
    Valued.v ((4:K)^k) = WithZero.exp (-(4*(k:ℤ))) := by
  let p := RamFieldPlace.rootIntegral
  let x : K := (p : K)
  have hne : p≠0 := by
    intro h
    have hp := RamFieldPlace.rootIntegral_sq
    change p^2=2 at hp
    rw [h,zero_pow (by decide)] at hp
    exact (by norm_num : (0:𝓞 F) ≠ 2) hp
  have hi : v.asIdeal = Ideal.span {p} :=
    (RamFieldPlace.eq_rootIdeal RamFieldPlace.two_mem).symm
  have hv : Valued.v x = WithZero.exp (-1:ℤ) := by
    calc
      Valued.v x = v.valuation F p := by
        exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K:=F) (v:=v) p
      _ = v.intValuation p := v.valuation_of_algebraMap (K:=F) p
      _ = _ := v.intValuation_singleton hne hi
  have h2 : x^2=(2:K) := by
    let f : 𝓞 F →+* K := (algebraMap F K).comp (algebraMap (𝓞 F) F)
    change (f p)^2=2
    rw [← map_pow,show p^2=2 from RamFieldPlace.rootIntegral_sq,map_ofNat]
  have h4 : x^4=(4:K) := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,h2]
    norm_num
  rw [←h4,←pow_mul,map_pow,hv,←WithZero.exp_nsmul]
  congr 1
  push_cast
  ring

/-- The two masses both occur, for any single admissible family, on the actual shell. -/
theorem exact_range (k : ℕ) (hk : 1≤k)
    (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    {D : ℝ≥0∞ | ∃ s : K, Valued.v s=Valued.v ((4:K)^k) ∧
      m (hermScal K conjG s) (latV gb v)=D} =
      ({(2+2/256^k), (2-2/256^k)} : Set ℝ≥0∞) := by
  ext D
  change (∃ s : K, Valued.v s=Valued.v ((4:K)^k) ∧
    m (hermScal K conjG s) (latV gb v)=D) ↔ _
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨s,hs,hD⟩
    obtain ⟨u,rfl⟩ := (valuation_shell k s).mp hs
    rw [original k hk u lam hlam m hm] at hD
    cases h : classBit u with
    | false => exact Or.inl (by rw [← hD,h]; rfl)
    | true => exact Or.inr (by rw [← hD,h]; rfl)
  · rintro (rfl|rfl)
    · let u := Units.map placeOrderMap.toMonoidHom (1:RamField.Oˣ)
      refine ⟨(4:K)^k*((u:v.adicCompletionIntegers F):K),(valuation_shell _ _).mpr ⟨u,rfl⟩,?_⟩
      rw [original k hk u lam hlam m hm]
      have e : classBit u=false := by
        unfold classBit u
        rw [model_roundtrip,RamDilate.UnitClass.bit_one]
      rw [e]
      rfl
    · let u := Units.map placeOrderMap.toMonoidHom RamDilate.UnitClass.twist
      refine ⟨(4:K)^k*((u:v.adicCompletionIntegers F):K),(valuation_shell _ _).mpr ⟨u,rfl⟩,?_⟩
      rw [original k hk u lam hlam m hm]
      have e : classBit u=true := by
        unfold classBit u
        rw [model_roundtrip,RamDilate.UnitClass.bit_twist]
      rw [e]
      rfl

theorem exact_range_at_exponent (k : ℕ) (hk : 1≤k)
    (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    {D : ℝ≥0∞ | ∃ s : K, Valued.v s=WithZero.exp (-(4*(k:ℤ))) ∧
      m (hermScal K conjG s) (latV gb v)=D} =
      ({(2+2/256^k), (2-2/256^k)} : Set ℝ≥0∞) := by
  simpa only [valuation_exponent] using exact_range k hk lam hlam m hm

theorem values_distinct (k : ℕ) : (2+(2:ℝ≥0∞)/256^k) ≠ 2-2/256^k := by
  intro h
  change UnitMass k false=UnitMass k true at h
  have e := congrArg ENNReal.toReal h
  rw [RamDilate.UnitClass.mass_real,RamDilate.UnitClass.mass_real] at e
  change 2+(2:ℝ)/256^k=2-(2:ℝ)/256^k at e
  have hp : 0<(2:ℝ)/256^k := by positivity
  linarith

/-- One family serves both masses at every positive scale. -/
theorem realized :
    ∃ lam : Measure K, IsStdV v lam ∧ ∃ m : H → Measure W, fam lam m ∧
      ∀ (k : ℕ), 1≤k →
      {D : ℝ≥0∞ | ∃ s : K, Valued.v s=Valued.v ((4:K)^k) ∧
        m (hermScal K conjG s) (latV gb v)=D} =
        ({(2+2/256^k), (2-2/256^k)} : Set ℝ≥0∞) := by
  obtain ⟨lam,hlam,m,hm,-⟩ := RamPlaceEndpoint.realized
  exact ⟨lam,hlam,m,hm,fun k hk => exact_range k hk lam hlam m hm⟩

end UnitTransport
#print axioms UnitTransport.original
#print axioms UnitTransport.valuation_shell
#print axioms UnitTransport.exact_range
#print axioms UnitTransport.values_distinct
#print axioms UnitTransport.realized
#print axioms UnitTransport.valuation_exponent
#print axioms UnitTransport.exact_range_at_exponent
