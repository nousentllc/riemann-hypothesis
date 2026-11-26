import DilateStableOddAll
import DilateEndpoint

open MeasureTheory Topology Filter Set
open scoped ENNReal NNReal
noncomputable section
namespace TargetFourHaar
open RamField RamDilate.OddCell RamDilate.StableOdd

local macro "haar_num" : tactic => `(tactic|
  (apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
   norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul,
     ENNReal.toReal_add, ENNReal.toReal_pow, ENNReal.toReal_ofNat]))

abbrev Gaussian := QuadraticAlgebra K (-1) 0
def putI (s : K) : Gaussian := ⟨0,s⟩

theorem putI_skew (s : K) : star (putI s) = -putI s := by
  ext <;> simp [putI]

/-- The literal skew element is represented by its imaginary scalar coordinate. -/
def skewCoord : K ≃ skewAdjoint Gaussian where
  toFun s := ⟨putI s, putI_skew s⟩
  invFun z := z.val.im
  left_inv _ := rfl
  right_inv z := by
    have h := congrArg QuadraticAlgebra.re (show star z.val = -z.val from z.property)
    simp only [QuadraticAlgebra.re_star,zero_mul,add_zero,QuadraticAlgebra.re_neg] at h
    have hz : (2:K)*z.val.re = 0 := by linear_combination h
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    apply Subtype.ext
    exact QuadraticAlgebra.ext hzero.symm rfl

/-- Coordinate Borel structure on the skew line. -/
local instance : MeasurableSpace (skewAdjoint Gaussian) :=
  MeasurableSpace.comap skewCoord.symm inferInstance

def skewBorel : K ≃ᵐ skewAdjoint Gaussian where
  toEquiv := skewCoord
  measurable_invFun := comap_measurable _
  measurable_toFun := by
    intro S hS
    obtain ⟨T,hT,rfl⟩ := hS
    simpa [Set.preimage_preimage] using hT

theorem split_coordinates (s t : K) :
    (algebraMap K Gaussian (2:K)⁻¹) * (-putI 1) * putI s + putI t =
      (⟨s/2,t⟩ : Gaussian) := by
  ext <;> simp [putI, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    div_eq_mul_inv] <;> ring

def half : K ≃+ K where
  toFun x := x/2
  invFun x := 2*x
  left_inv x := by dsimp; field_simp
  right_inv x := by dsimp; field_simp
  map_add' x y := add_div _ _ _

theorem half_preimage : half ⁻¹' integers = cylinder 1 0 := by
  have h := even_cell 1 (0:O)
  simp only [map_zero] at h
  rw [← h]
  ext x
  change x/2 ∈ Set.range inc ↔ x ∈ inc '' {z : O | (pi:O)^(2*1) ∣ z-0}
  simp only [Nat.mul_one, pi_sq, sub_zero]
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨2*y, ⟨y,rfl⟩, ?_⟩
    rw [map_mul,map_ofNat,hy]; field_simp
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    refine ⟨w,?_⟩
    rw [map_mul,map_ofNat]; field_simp

theorem half_push (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    lam.map half = (1/4 : ℝ≥0∞) • lam := by
  have hc : Continuous half := by change Continuous (fun x : K => x/2); fun_prop
  have hi : Continuous half.symm := by change Continuous (fun x : K => 2*x); fun_prop
  let : (lam.map half).IsAddHaarMeasure := half.isAddHaarMeasure_map lam hc hi
  let c := Measure.addHaarScalarFactor (lam.map half) lam
  have he : lam.map half = c • lam := Measure.isAddLeftInvariant_eq_smul _ _
  have hb := congrArg (fun m : Measure K => m integers) he
  change (lam.map half) integers = (c • lam) integers at hb
  rw [Measure.map_apply hc.measurable integers_open.measurableSet,half_preimage,
    cyl_mass lam hvol,Measure.smul_apply,hvol] at hb
  have hco : (c:ℝ≥0∞) = 1/4 := by
    simpa [ENNReal.smul_def, show (2:ℝ≥0∞)^2=4 by norm_num] using hb.symm
  rw [he, ←hco]; rfl

def split : K × K → K × K := Prod.map half id

theorem split_push (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (lam.prod lam).map split = (1/4 : ℝ≥0∞) • lam.prod lam := by
  change (lam.prod lam).map (Prod.map half id) = _
  have hc : Measurable half := by change Measurable (fun x : K => x/2); fun_prop
  rw [←Measure.map_prod_map lam lam hc measurable_id,Measure.map_id,half_push lam hvol,
    Measure.prod_smul_left]

theorem split_matched (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (((2:ℝ≥0∞) • lam).prod ((2:ℝ≥0∞) • lam)).map split = lam.prod lam := by
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.map_smul,Measure.map_smul,
    split_push lam hvol,smul_smul,smul_smul]
  rw [show ((2:ℝ≥0∞)*2)*(1/4)=1 by haar_num,one_smul]

theorem split_scaled (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (c : ℝ≥0∞) : ((c • lam).prod (c • lam)).map split =
      (c*c*(1/4:ℝ≥0∞)) • lam.prod lam := by
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.map_smul,Measure.map_smul,
    split_push lam hvol,smul_smul,smul_smul]

/-- The split determines the target Haar uniquely when the Gaussian source volumes agree. -/
theorem forced_target (lam nu : Measure K) [lam.IsAddHaarMeasure] [nu.IsAddHaarMeasure]
    (hvol : lam integers = 1) (hs : (nu.prod nu).map split = lam.prod lam) :
    nu = (2:ℝ≥0∞) • lam := by
  let c := Measure.addHaarScalarFactor nu lam
  have he : nu = c • lam := Measure.isAddLeftInvariant_eq_smul _ _
  have hco : nu = (c:ℝ≥0∞) • lam := he
  rw [hco,split_scaled lam hvol] at hs
  have h := congrArg (fun m : Measure (K × K) => m (integers ×ˢ integers)) hs
  change ((_ : ℝ≥0∞) • lam.prod lam) _ = (lam.prod lam) _ at h
  simp only [Measure.smul_apply,smul_eq_mul,Measure.prod_prod,hvol,mul_one] at h
  have hr := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.coe_toReal,ENNReal.toReal_ofNat,
    ENNReal.toReal_one] at hr
  have h2 : (c:ℝ) = 2 := by nlinarith [c.coe_nonneg]
  have hc : c = 2 := by exact_mod_cast h2
  rw [hco,hc]; rfl

def ball (r : ℕ) := cylinder r (digit r (4:O))

theorem ball_mass (r : ℕ) (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    lam (ball r) = 1 / (2^r : ℝ≥0∞)^2 := cyl_mass lam hvol _ _

theorem tail_tube (n : ℕ) (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (ball (n+3))) =
      (257/128 : ℝ≥0∞) * lam (ball (n+3)) := by
  have h := DilateTransport.tube 1 (n+3) 1 lam hvol
  have hc := RamDilate.counts 1 (by decide) n
  norm_num at hc
  specialize h (by simpa [RamDilate.den] using hc)
  norm_num [ball] at h ⊢
  rw [h, show (2+2/256:ℝ≥0∞)=257/128 by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div,ENNReal.toReal_ofNat]]

theorem ball_four (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    lam (ball 3) = 1/64 ∧ ((2:ℝ≥0∞) • lam) (ball 3) = 1/32 ∧
    (Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (ball 3)) = 257/8192 := by
  have h := tail_tube 0 lam hvol
  have hb := ball_mass 3 lam hvol
  norm_num at hb
  simp only [Nat.zero_add,hb] at h
  refine ⟨by simpa using hb,?_,?_⟩
  · rw [Measure.smul_apply,hb,smul_eq_mul]; haar_num
  · rw [h]; haar_num

theorem literal_skew_ball (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    let B := skewBorel '' ball 3
    lam.map skewBorel B = 1/64 ∧ ((2:ℝ≥0∞) • lam.map skewBorel) B = 1/32 := by
  dsimp only
  have hS : MeasurableSet (skewBorel '' ball 3) := skewBorel.measurableSet_image.mpr (open_cylinder 3 (digit 3 (4:O))).measurableSet
  rw [Measure.smul_apply,Measure.map_apply skewBorel.measurable hS,
    Set.preimage_image_eq _ skewBorel.injective,(ball_four lam hvol).1]
  exact ⟨rfl,by rw [smul_eq_mul]; haar_num⟩

/-- Cofinal integral identities plus continuity at four identify the point value. -/
theorem identify_regular (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (f : K → ℝ) (D : ℝ) (hcont : ContinuousAt f 4)
    (hint : ∀ n, IntegrableOn f (ball (n+5)) lam)
    (havg : ∀ n, ∫ x in ball (n+5), f x ∂lam = D * lam.real (ball (n+5))) : f 4 = D := by
  by_contra hne
  let ε := |D - f 4| / 2
  have hε : 0 < ε := half_pos (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)))
  have hN : {x | dist (f x) (f 4) < ε} ∈ 𝓝 (4:K) := hcont (Metric.ball_mem_nhds _ hε)
  obtain ⟨n, hn⟩ := small_four _ hN
  have hsub : ball (n+5) ⊆ {x | dist (f x) (f 4) < ε} := by
    simpa [ball,map_ofNat] using hn
  have hfinite : lam (ball (n+5)) < ⊤ := (compact_cylinder _ _).measure_lt_top
  have hpos : 0 < lam.real (ball (n+5)) := by
    rw [Measure.real,ball_mass _ lam hvol,ENNReal.toReal_div,ENNReal.toReal_one,
      ENNReal.toReal_pow,ENNReal.toReal_pow,ENNReal.toReal_ofNat]; positivity
  have hbound := norm_setIntegral_le_of_norm_le_const (f := fun x => f x - f 4)
    hfinite (fun x hx => (show ‖f x - f 4‖ = dist (f x) (f 4) by rw [dist_eq_norm]).trans_le (hsub hx).le)
  rw [integral_sub (hint n) (integrableOn_const hfinite.ne),havg,setIntegral_const,
    smul_eq_mul,mul_comm (lam.real _) (f 4),←sub_mul,Real.norm_eq_abs,abs_mul,abs_of_pos hpos] at hbound
  have hle := (mul_le_mul_iff_left₀ hpos).mp hbound
  dsimp [ε] at hε hle
  linarith

/-- Identify a regular candidate directly from equality of its weighted slab integrals
with the actual six-square source masses on a cofinal sequence. -/
theorem candidate_at_four (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (f : K → ℝ) (hcont : ContinuousAt f 4)
    (hint : ∀ n, IntegrableOn f (ball (n+5)) lam)
    (hslabs : ∀ n, 2 * (∫ x in ball (n+5), f x ∂lam) =
      ((Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (ball (n+5)))).toReal) :
    f 4 = 257/256 := by
  apply identify_regular lam hvol f _ hcont hint
  intro n
  have h := hslabs n
  have ht := tail_tube (n+2) lam hvol
  rw [show n+2+3=n+5 by omega] at ht
  rw [ht,ENNReal.toReal_mul] at h
  norm_num [ENNReal.toReal_div,ENNReal.toReal_ofNat] at h
  change _ = (257/256) * (lam _).toReal
  linarith

/-- The Jacobian factors for one scalar Haar and three Gaussian source coordinates. -/
theorem scaling_law (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hsplit : c^2 / 4 = a) :
    c = 2 * Real.sqrt a ∧
    (a^3/c = 1 ↔ a^5 = 4) := by
  constructor
  · nlinarith [Real.sq_sqrt ha.le, Real.sqrt_nonneg a,
      mul_self_inj_of_nonneg hc.le (by positivity : 0 ≤ 2*Real.sqrt a)]
  constructor
  · intro he
    have h := (div_eq_iff hc.ne').mp he
    have h6 : a^6 = 4*a := by calc
      a^6 = (a^3)^2 := by ring
      _ = 4*a := by nlinarith [show a^3 = c by linarith]
    apply (mul_left_cancel₀ ha.ne' : a * a^5 = a * 4 → a^5=4)
    nlinarith only [h6]
  · intro he
    apply (div_eq_iff hc.ne').mpr
    have hp : (a^3)^2 = c^2 := by calc
      (a^3)^2 = a * a^5 := by ring
      _ = c^2 := by rw [he]; linarith
    rw [one_mul]
    exact (mul_self_inj_of_nonneg (by positivity : 0 ≤ a^3) hc.le).mp (by simpa only [pow_two] using hp)

/-- Doubling target Haar and halving the scalar density preserves every integrated test. -/
theorem integral_compensation {X : Type*} [MeasurableSpace X] (mu : Measure X) (f : X → ℝ≥0∞) :
    (∫⁻ x, (1/2:ℝ≥0∞)*f x ∂((2:ℝ≥0∞) • mu)) = ∫⁻ x, f x ∂mu := by
  rw [lintegral_smul_measure,lintegral_const_mul' _ _ (by finiteness)]
  change (2:ℝ≥0∞)*((1/2)*_) = _
  rw [←mul_assoc, show (2:ℝ≥0∞)*(1/2)=1 by haar_num,one_mul]

/-- Apply the cofinal test in literal skew target coordinates and with the split Haar. -/
theorem skew_candidate_at_four (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1)
    (g : skewAdjoint Gaussian → ℝ) (hc : ContinuousAt (fun x => g (skewBorel x)) 4)
    (hi : ∀ n, IntegrableOn (fun x => g (skewBorel x)) (ball (n+5)) lam)
    (hs : ∀ n, (∫ t in skewBorel '' ball (n+5), g t ∂((2:ℝ≥0∞) • lam.map skewBorel)) =
      ((Measure.pi fun _ : TargetOne.Idx => lam) (RamTransport.tube K integers (ball (n+5)))).toReal) :
    g (skewBorel 4) = 257/256 := by
  apply candidate_at_four lam hvol (fun x => g (skewBorel x)) hc hi
  intro n
  have h := hs n
  rw [Measure.restrict_smul,integral_smul_measure,setIntegral_map_equiv,
    Set.preimage_image_eq _ skewBorel.injective] at h
  simpa only [ENNReal.toReal_ofNat,smul_eq_mul] using h

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (IsFibreFamily)

/-- Rescale the original regular-family definition itself, including support and test continuity. -/
theorem rescale_regular_family {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {mu : Measure V} {f : V → Y} {i : X → Y}
    {U : Set V} {nu : Measure X} {B : Set X} {m : X → Measure V}
    (h : IsFibreFamily mu f i U nu B m) :
    IsFibreFamily mu f i U ((2:ℝ≥0∞) • nu) B (fun b => (1/2:ℝ≥0∞) • m b) := by
  refine ⟨?_,?_,?_⟩
  · intro b
    rw [Measure.smul_apply,h.1 b,smul_zero]
  · intro phi hphi
    rw [h.2.1 phi hphi]
    simp_rw [lintegral_smul_measure (1/2:ℝ≥0∞) phi,smul_eq_mul]
    exact (integral_compensation nu (fun b => ∫⁻ v, phi v ∂m b)).symm
  · intro phi hc hs hu
    obtain ⟨hi,hc'⟩ := h.2.2 phi hc hs hu
    refine ⟨fun b hb => (hi b hb).smul_measure (by finiteness), ?_⟩
    simp only [integral_smul_measure,smul_eq_mul]
    exact continuousOn_const.mul hc'

/-- The cyclotomic order generated by zeta with zeta² - pi*zeta + 1 = 0. -/
abbrev ZetaOrder := QuadraticAlgebra O (-1) (pi:O)

theorem zeta_order_no_trace_one (z : ZetaOrder) : z + star z ≠ 1 := by
  intro h
  have h' := congrArg (fun x : ZetaOrder => x.re.re) h
  have hp : (pi : O).re = 0 := rfl
  have hp' : (pi : O).im = 1 := rfl
  simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.re_star,QuadraticAlgebra.re_mul,
    hp,hp',zero_mul,zero_add,QuadraticAlgebra.re_one] at h'
  have ht : 2 * (z.re.re + z.im.im) = 1 := by linear_combination h'
  have hz := congrArg (PadicInt.toZModPow 1) ht
  rw [map_mul,map_ofNat,map_one,show (2:ZMod (2^1))=0 by decide,zero_mul] at hz
  exact (by decide : (0:ZMod (2^1))≠1) hz

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open RamGlobal (F gb conjG)
open RamPlaceEndpoint (v H W fam)

theorem named_regular_value (lam : Measure RamPlaceEndpoint.K) (hlam : IsStdV v lam)
    (m : H → Measure W) (hm : fam lam m) :
    ((1/2:ℝ≥0∞) • m (hermScal RamPlaceEndpoint.K conjG 4)) (latV gb v) = 257/256 := by
  have h := RamPlaceEndpoint.original lam hlam m hm
  rw [Measure.smul_apply]
  change (1/2:ℝ≥0∞) * m RamPlaceEndpoint.atFour (latV gb v) = _
  rw [h]; haar_num

theorem realized_rescaled :
    ∃ lam : Measure RamPlaceEndpoint.K, IsStdV v lam ∧ ∃ m' : H → Measure W,
      IsGramFib RamPlaceEndpoint.K conjG RamBridge.J 1 (coordW RamPlaceEndpoint.K gb lam 1 3)
        ((2:ℝ≥0∞) • coordHerm RamPlaceEndpoint.K conjG gb lam 1) m' ∧
      m' RamPlaceEndpoint.atFour (latV gb v) = 257/256 := by
  obtain ⟨lam,hl,m,hm,_⟩ := RamPlaceEndpoint.realized
  exact ⟨lam,hl,(fun b => (1/2:ℝ≥0∞) • m b),rescale_regular_family hm,
    named_regular_value lam hl m hm⟩

theorem pure_relabel_fails_split (lam : Measure K) [lam.IsAddHaarMeasure] (hvol : lam integers = 1) :
    (lam.prod lam).map split ≠ lam.prod lam := by
  intro h
  have he := forced_target lam lam hvol h
  have hh := congrArg (fun m : Measure K => m integers) he
  change lam integers = ((2:ℝ≥0∞) • lam) integers at hh
  rw [Measure.smul_apply,smul_eq_mul,hvol,mul_one] at hh
  exact (by norm_num : (1:ℝ≥0∞) ≠ 2) hh

end TargetFourHaar

#print axioms TargetFourHaar.putI_skew
#print axioms TargetFourHaar.split_coordinates
#print axioms TargetFourHaar.half_preimage
#print axioms TargetFourHaar.half_push
#print axioms TargetFourHaar.split_push
#print axioms TargetFourHaar.split_matched
#print axioms TargetFourHaar.ball_mass
#print axioms TargetFourHaar.tail_tube
#print axioms TargetFourHaar.ball_four
#print axioms TargetFourHaar.scaling_law
#print axioms TargetFourHaar.integral_compensation
#print axioms TargetFourHaar.named_regular_value

#print axioms TargetFourHaar.skewCoord
#print axioms TargetFourHaar.literal_skew_ball
#print axioms TargetFourHaar.identify_regular

#print axioms TargetFourHaar.split_scaled
#print axioms TargetFourHaar.forced_target
#print axioms TargetFourHaar.candidate_at_four

#print axioms TargetFourHaar.skew_candidate_at_four
#print axioms TargetFourHaar.rescale_regular_family
#print axioms TargetFourHaar.zeta_order_no_trace_one

#print axioms TargetFourHaar.realized_rescaled
#print axioms TargetFourHaar.pure_relabel_fails_split
