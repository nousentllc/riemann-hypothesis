import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Uriel.WindowMass
open Deduction

def density (F : CharFamily) (θ y : ℝ) : ℝ := max (Gm F y) 0 * y ^ (-θ - 1)

def mass (F : CharFamily) (θ δ Y : ℝ) : ℝ :=
  ∫ y in Icc Y (Y ^ (1 + δ)), density F θ y

theorem integrable_density (F : CharFamily) {θ a b : ℝ} (hθ : 0 < θ) (ha : 1 ≤ a) :
    IntegrableOn (density F θ) (Icc a b) := by
  classical
  obtain ⟨Φ, hP⟩ := poleData F
  obtain ⟨C, hC⟩ := hP.growth
  have hm : Measurable (Gm F) := Finset.measurable_sum _ fun i _ => measurable_const.mul
    (Complex.measurable_re.comp (measurable_Gchi (F.χ i)))
  have md : Measurable (density F θ) := by
    unfold density
    fun_prop
  apply IntegrableOn.of_bound measure_Icc_lt_top md.aestronglyMeasurable (|C| * b ^ 2)
  apply (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall ?_)
  intro y hy
  have hy1 := ha.trans hy.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hz := hC (Real.log y) (Real.log_nonneg hy1)
  rw [gm, Real.exp_log hy0, two_mul, Real.exp_add, Real.exp_log hy0, ← sq] at hz
  have hpos : 0 ≤ max (Gm F y) 0 := le_max_right _ _
  have hpow : 0 ≤ y ^ (-θ - 1) := Real.rpow_nonneg hy0.le _
  rw [density, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos hpow)]
  calc
    max (Gm F y) 0 * y ^ (-θ - 1) ≤ max (Gm F y) 0 * 1 :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)) hpos
    _ ≤ |Gm F y| := by rw [mul_one]; exact max_le (le_abs_self _) (abs_nonneg _)
    _ ≤ C * y ^ 2 := hz
    _ ≤ |C| * b ^ 2 := by gcongr <;> first | exact le_abs_self _ | exact hy.2

theorem forced_mass (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    {i : F.ι} {ρ : ℂ} (hx : θ < ρ.re) (hzero : DirichletCharacter.LFunction (F.χ i) ρ = 0) :
    ∃ η : ℝ, 0 < η ∧ ∃ T : ℝ, ∀ Y ≥ T, Y ^ η < mass F θ δ Y := by
  by_contra! h
  apply lemmaL F hθ hθ1 hδ _ i ρ hx hzero
  intro η hη Y₀
  obtain ⟨Y, hY, hm⟩ := h η hη (max 1 Y₀)
  refine ⟨Y, (le_max_right _ _).trans hY, fun y => max (Gm F y) 0,
    integrable_density F hθ ((le_max_left _ _).trans hY), fun y _ => ⟨le_max_right _ _, le_max_left _ _⟩, hm⟩

#print axioms integrable_density
#print axioms forced_mass

theorem suffix_weight (F : CharFamily) {θ s Y Z B : ℝ} (hθ : 0 < θ) (hs : θ ≤ s)
    (hY : 1 ≤ Y) (hZ : Y ≤ Z) :
    Z ^ (s - θ) * (∫ y in Icc Z B, density F s y) ≤ ∫ y in Icc Y B, density F θ y := by
  have hZ1 := hY.trans hZ
  rw [← integral_const_mul]
  apply le_trans (setIntegral_mono_on
    ((integrable_density F (hθ.trans_le hs) hZ1).const_mul (Z ^ (s - θ)))
    (integrable_density F hθ hZ1) measurableSet_Icc ?_)
  · apply setIntegral_mono_set (integrable_density F hθ hY)
    · apply (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall ?_)
      intro y hy
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by linarith [hy.1] : 0 ≤ y) _)
    · exact Filter.Eventually.of_forall (Icc_subset_Icc_left hZ)
  · intro y hy
    have hy0 : 0 < y := zero_lt_one.trans_le (hZ1.trans hy.1)
    have hp := Real.rpow_le_rpow (zero_le_one.trans hZ1) hy.1 (sub_nonneg.mpr hs)
    calc
      Z ^ (s - θ) * density F s y ≤ y ^ (s - θ) * density F s y :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hy0.le _))
      _ = density F θ y := by
        unfold density
        rw [mul_left_comm, ← Real.rpow_add hy0]
        congr 2; ring

theorem forced_power (F : CharFamily) {θ δ b : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    {i : F.ι} {ρ : ℂ} (hx : θ < ρ.re) (hzero : DirichletCharacter.LFunction (F.χ i) ρ = 0)
    (hb : b < (1+δ)*(ρ.re-θ)) :
    ∃ T : ℝ, ∀ Y ≥ T, Y ^ b < mass F θ δ Y := by
  have hβ : ρ.re < 1 := by
    by_contra! h
    exact charFamily_LFunction_ne_zero_of_one_le_re F i ρ h hzero
  have hgap : 0 < ρ.re-θ := sub_pos.mpr hx
  obtain ⟨a, ha0, haend⟩ := exists_between (max_lt (by linarith : (1 : ℝ) < 1+δ)
    ((div_lt_iff₀ hgap).2 hb))
  have ha1 := (le_max_left _ _).trans_lt ha0
  have ha : 0 < a := zero_lt_one.trans ha1
  have ha' : b < a*(ρ.re-θ) := (div_lt_iff₀ hgap).1 ((le_max_right _ _).trans_lt ha0)
  have htest : θ + b/a < ρ.re := by
    have := (div_lt_iff₀ ha).2 (show b < (ρ.re-θ)*a by linarith [mul_comm a (ρ.re-θ)])
    linarith
  obtain ⟨s, hs0, hsβ⟩ := exists_between (max_lt hx htest)
  have hsθ := (le_max_left _ _).trans_lt hs0
  have hb' : b < a*(s-θ) := by
    rw [mul_comm a]
    apply (div_lt_iff₀ ha).1
    linarith [(le_max_right _ _).trans_lt hs0]
  let δ' := (1+δ)/a-1
  have hd : 0 < δ' := by
    dsimp [δ']; apply sub_pos.mpr; rw [lt_div_iff₀ ha,one_mul]; exact haend
  obtain ⟨η,hη,T,hT⟩ := forced_mass F (hθ.trans hsθ) (hsβ.trans hβ) hd hsβ hzero
  refine ⟨max 1 T,fun Y hY => ?_⟩
  have hY1 := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hZY : Y ≤ Y ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_le hY1 ha1.le
  have hZT : T ≤ Y ^ a := ((le_max_right _ _).trans hY).trans hZY
  have hpos : 0 < (Y ^ a) ^ (s-θ) := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hY0 _) _
  have hend : (Y ^ a) ^ (1+δ') = Y ^ (1+δ) := by
    rw [← Real.rpow_mul hY0.le]; congr 1; dsimp [δ']; field_simp; ring
  have hmass := hT (Y ^ a) hZT
  have hw := suffix_weight F hθ hsθ.le hY1 hZY (B := Y ^ (1+δ))
  unfold mass at hmass ⊢
  rw [hend] at hmass
  have hone : 1 ≤ (Y^a)^η := Real.one_le_rpow (hY1.trans hZY) hη.le
  calc
    Y ^ b ≤ Y ^ (a*(s-θ)) := Real.rpow_le_rpow_of_exponent_le hY1 hb'.le
    _ = (Y ^ a) ^ (s-θ) := Real.rpow_mul hY0.le _ _
    _ < (Y ^ a) ^ (s-θ) * ∫ y in Icc (Y ^ a) (Y ^ (1+δ)), density F s y :=
      lt_mul_of_one_lt_right hpos (hone.trans_lt hmass)
    _ ≤ _ := hw

#print axioms suffix_weight
#print axioms forced_power

end Uriel.WindowMass

