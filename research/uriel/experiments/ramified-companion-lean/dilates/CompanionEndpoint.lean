import DilateTransport
import CompanionCells

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory Topology
open NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix
noncomputable section
namespace CompanionTransport
open RamGlobal (F E conjG gb)
open RamPlaceEndpoint (v K H W fam)

/-- The unit group is that of the *original place's* valuation ring. -/
abbrev IntegralUnits := (v.adicCompletionIntegers F)ˣ

/-- The fixed model uniformizer, carried to the named place by its field isomorphism. -/
def uniformizer : K :=
  RamPlaceCompletion.e.symm (RamField.inc (RamDilate.OddCell.pi : RamField.O))

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

/-- The companion mass on the original lattice, for every admissible
normalized Haar measure and disintegrating fiber family. -/
theorem original (k : ℕ) (hk : 1≤k) (u : IntegralUnits)
    (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    m (hermScal K conjG ((4:K)^k * (1+uniformizer) * ((u : v.adicCompletionIntegers F) : K)^2)) (latV gb v) =
      RamDilate.Companion.mass k := by
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
  let s : K := 4^k * (1+uniformizer) * ((u : v.adicCompletionIntegers F) : K)^2
  obtain ⟨w,hw⟩ := liftUnit u
  let a : RamField.O := (w:RamField.O)^2 * RamDilate.Companion.centerAt k
  have ep : e uniformizer = RamField.inc (RamDilate.OddCell.pi : RamField.O) :=
    e.apply_symm_apply _
  have hw' : RamField.inc (w:RamField.O) = e ((u : v.adicCompletionIntegers F) : K) := hw
  have es : e s = RamField.inc a := by
    simp only [s,a,RamDilate.Companion.centerAt,map_mul,map_pow,map_ofNat,map_add,map_one,ep,←hw']
    ring
  have hs : s ≠ 0 := by
    have hw0 := (Units.map RamField.inc.toMonoidHom w).ne_zero
    have h4 : (4:RamField.K) ≠ 0 := by norm_num
    have hunit : IsUnit (1+(RamDilate.OddCell.pi:RamField.O)) :=
      RamDilate.Companion.twist_isUnit
    have hcz : RamField.inc (1+(RamDilate.OddCell.pi:RamField.O)) ≠ 0 :=
      (hunit.map RamField.inc.toMonoidHom).ne_zero
    intro h
    have h' : RamField.inc a = 0 := es.symm.trans ((congrArg e h).trans (map_zero _))
    simp only [a,RamDilate.Companion.centerAt,map_mul,map_pow,map_ofNat] at h'
    exact mul_ne_zero (pow_ne_zero _ hw0) (mul_ne_zero (pow_ne_zero _ h4) hcz) h'
  apply RamTransportForm.original_mass conjG RamBridge.J gb K RamGlobal.isCM RamGlobal.herm_id
    RamGlobal.gram_matrix hl O' hcompact hopen lam hlam.1 m hm s hs
      (RamDilate.Companion.mass k) (RamDilate.Companion.mass_positive k hk)
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
    have ht := RamDilate.Companion.all_late k (2*r) hk (by dsimp [r,r0]; omega) w μ hv
    dsimp only at ht
    rw [RamDilate.StableOdd.even_cell] at ht
    exact ht

theorem mass_one : RamDilate.Companion.mass 1 = (255/128:ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (RamDilate.Companion.mass_finite 1) (by finiteness)).mp
  norm_num [RamDilate.Companion.mass_real,ENNReal.toReal_div]

theorem mass_two : RamDilate.Companion.mass 2 = (65535/32768:ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (RamDilate.Companion.mass_finite 2) (by finiteness)).mp
  norm_num [RamDilate.Companion.mass_real,ENNReal.toReal_div]

/-- The disintegrating family is chosen once, before all scales and all local units. -/
theorem realized :
    ∃ lam : Measure K, IsStdV v lam ∧ ∃ m : H → Measure W, fam lam m ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ u : IntegralUnits,
        m (hermScal K conjG ((4:K)^k * (1+uniformizer) * ((u : v.adicCompletionIntegers F) : K)^2)) (latV gb v) =
          RamDilate.Companion.mass k := by
  obtain ⟨lam,hlam,m,hm,-⟩ := RamPlaceEndpoint.realized
  exact ⟨lam,hlam,m,hm,fun k hk u => original k hk u lam hlam m hm⟩

end CompanionTransport
#print axioms CompanionTransport.original
#print axioms CompanionTransport.realized
#print axioms CompanionTransport.mass_one
#print axioms CompanionTransport.mass_two
