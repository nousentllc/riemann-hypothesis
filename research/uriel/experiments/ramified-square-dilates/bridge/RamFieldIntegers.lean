import RamField
open MeasureTheory Topology
noncomputable section
namespace RamField

/-- The element represented by the second basis vector is the ramified uniformizer. -/
def uniformizer : K := ⟨0,1⟩

theorem uniformizer_sq : uniformizer ^ 2 = (2:K) := by
  ext <;> norm_num [pow_two,uniformizer,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

theorem uniformizer_norm_sq : ‖uniformizer‖ ^ 2 = 1/2 := by
  rw [← norm_pow,uniformizer_sq, ← map_ofNat (algebraMap ℚ_[2] K) 2, norm_algebraMap']
  simpa using (Padic.norm_p (p:=2))

private theorem no_norm_tie (a b : ℚ_[2]) (ha:a≠0) (hb:b≠0) :
    ‖a‖ ≠ ‖b‖ * ‖uniformizer‖ := by
  intro h
  have hn : ‖a^2‖ = ‖(2:ℚ_[2])*b^2‖ := by
    rw [norm_pow,norm_mul,norm_pow,h,mul_pow,uniformizer_norm_sq]
    have hp : ‖(2:ℚ_[2])‖ = 1/2 := by simpa using (Padic.norm_p (p:=2))
    rw [hp]; ring
  have hp : (2 : ℚ_[2]).valuation=1 := Padic.valuation_p
  rw [Padic.norm_eq_zpow_neg_valuation (pow_ne_zero _ ha),
    Padic.norm_eq_zpow_neg_valuation (mul_ne_zero (by norm_num) (pow_ne_zero _ hb)),
    zpow_right_inj₀ (by norm_num) (by norm_num),Padic.valuation_pow,
    Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb),Padic.valuation_pow,hp] at hn
  omega

theorem coordinate_norm (x : K) : ‖x‖ = max ‖x.re‖ (‖x.im‖ * ‖uniformizer‖) := by
  let f := algebraMap ℚ_[2] K
  have hx : x = f x.re + f x.im * uniformizer := by
    ext <;> simp [f,uniformizer,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im]
  have hf (y:ℚ_[2]) : ‖f y‖=‖y‖ := norm_algebraMap' K y
  by_cases ha : x.re=0
  · conv_lhs => rw [hx,ha,map_zero,zero_add,norm_mul,hf]
    simp [ha,mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  by_cases hb : x.im=0
  · conv_lhs => rw [hx,hb,map_zero,zero_mul,add_zero,hf]
    simp [hb]
  have hne : ‖f x.re‖ ≠ ‖f x.im * uniformizer‖ := by
    rw [norm_mul,hf,hf]; exact no_norm_tie _ _ ha hb
  conv_lhs => rw [hx,IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne,norm_mul,hf,hf]

private theorem padic_large {a : ℚ_[2]} (ha : 1 < ‖a‖) : 2 ≤ ‖a‖ := by
  have hn : a≠0 := by intro h; rw [h,norm_zero] at ha; linarith
  rw [Padic.norm_eq_zpow_neg_valuation hn] at ha ⊢
  have hv : 0 < -a.valuation := by
    apply (zpow_lt_zpow_iff_right₀ (a:= (2:ℝ)) (by norm_num)).mp
    simpa using ha
  have : (2:ℝ)^(1:ℤ) ≤ 2^(-a.valuation) :=
    (zpow_le_zpow_iff_right₀ (by norm_num)).mpr (by omega)
  simpa using this

/-- The coordinate order is precisely the spectral norm unit ball, including at the ramified prime. -/
theorem integers_eq_unit_ball : integers = Metric.closedBall (0:K) 1 := by
  ext x
  rw [Metric.mem_closedBall,dist_zero_right,coordinate_norm,max_le_iff]
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨y.re.2,?_⟩
    have h := mul_le_mul_of_nonneg_right y.im.2 (norm_nonneg uniformizer)
    change ‖(y.im : ℚ_[2])‖ * ‖uniformizer‖ ≤ 1
    have hs := uniformizer_norm_sq
    nlinarith [norm_nonneg uniformizer]
  · rintro ⟨ha,hb⟩
    have hh : ‖x.im‖ ≤ 1 := by
      by_contra! hn
      have hm := mul_le_mul_of_nonneg_right (padic_large hn) (norm_nonneg uniformizer)
      have hs := uniformizer_norm_sq
      nlinarith [norm_nonneg uniformizer, sq_nonneg (‖uniformizer‖-1/2)]
    exact ⟨⟨⟨x.re,ha⟩,⟨x.im,hh⟩⟩,rfl⟩

end RamField
#print axioms RamField.integers_eq_unit_ball
