import ScaleControl

open New
set_option exponentiation.threshold 1200
namespace SelectedPlace
noncomputable section

theorem logB_le_m {P : Parameters} (D : Data P) : D.logB ≤ (D.m : ℝ) := by
  by_contra! h
  have hm : (1 : ℝ) ≤ D.m := by
    obtain ⟨e, he, -⟩ := D.exists_m_eq_two_pow
    have hm : 0 < D.m := by rw [he]; positivity
    exact_mod_cast hm
  have hs : (D.m : ℝ) ^ 2 < D.logB ^ 2 :=
    pow_lt_pow_left₀ h (by positivity) (by decide)
  have ht : D.logB ^ 2 ≤ D.logB ^ 100 :=
    pow_le_pow_right₀ (hm.trans h.le) (by decide)
  exact (not_lt_of_ge (ht.trans (D.logB_pow_le_x.trans D.m_sq_mem_Icc.1))) hs

theorem selected_lower {P : Parameters} (D : Data P) : D.m ^ 21 ≤ D.bPlaces.card := by
  obtain ⟨e, he, hs⟩ := D.exists_m_eq_two_pow
  have hm : (0 : ℝ) < D.m := by rw [he]; positivity
  have hpow : D.m ^ 22 = 2 ^ D.towerExp := by rw [he, hs, pow_mul]
  have hfac : 2 ^ D.towerExp ≤ towerDeg D.towerExp := by
    unfold towerDeg
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have h₁ := D.towerDeg_le_card_bPlaces_mul
  have h₂ : (2 ^ D.towerExp : ℕ) ≤ towerDeg D.towerExp := hfac
  have h₃ : ((D.m : ℝ) ^ 22) ≤ (towerDeg D.towerExp : ℝ) := by rw [← Nat.cast_pow, hpow]; exact_mod_cast h₂
  have h₄ := h₃.trans (h₁.trans (mul_le_mul_of_nonneg_left (logB_le_m D) (by positivity)))
  have h₅ : ((D.m : ℝ) ^ 21) ≤ D.bPlaces.card := by
    apply (mul_le_mul_iff_left₀ hm).mp
    calc
      (D.m : ℝ) ^ 21 * (D.m : ℝ) = (D.m : ℝ) ^ 22 := by ring
      _ ≤ (D.bPlaces.card : ℝ) * D.m := h₄
  exact_mod_cast h₅

theorem selected_large {P : Parameters} (D : Data P) : 2 ^ 1071 ≤ D.bPlaces.card := by
  have hX : (2 : ℝ) ^ 100 < D.x := by
    rw [New.Data.x, D.exp_logX]
    exact_mod_cast FixedDatum.scale_floor D
  have hbig : (2 : ℝ) ^ 50 < D.m := by
    by_contra! h
    have hle : (D.m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 50) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h _
    have hx := hX.trans_le (D.m_sq_mem_Icc.1.trans hle)
    rw [← pow_mul] at hx
    exact (lt_irrefl _) hx
  obtain ⟨e, he, -⟩ := D.exists_m_eq_two_pow
  have hexp : 51 ≤ e + 1 := by
    by_contra! h
    have hm : (D.m : ℝ) ≤ (2 : ℝ) ^ 50 := by
      rw [he, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge hm) hbig
  have hm : 2 ^ 51 ≤ D.m := by
    rw [he]
    exact Nat.pow_le_pow_right (by decide) hexp
  have hpow : (2 ^ 51 : ℕ) ^ 21 ≤ D.m ^ 21 := by gcongr
  rw [← pow_mul] at hpow
  exact hpow.trans (selected_lower D)

theorem actual_selected :
    FixedDatum.controlDatum.natX = FixedDatum.fixedN ∧
      2 ^ 1071 ≤ FixedDatum.controlDatum.bPlaces.card ∧
      ∀ σ ∈ FixedDatum.controlDatum.bPlaces,
        FixedDatum.controlParameters.placeClass
          (FixedDatum.controlParameters.q₀.dvd_mul_right
            (towerDeg FixedDatum.controlDatum.towerExp)) σ = -1 :=
  ⟨FixedDatum.same_integer.2, selected_large _, FixedDatum.controlDatum.placeClass_of_mem_bPlaces⟩

/-- Readable labels exist on this very set, with no reselection. -/
def actual_labels : FixedDatum.controlDatum.bPlaces ↪
    (ZMod FixedDatum.controlDatum.q₁)ˣ where
  toFun v := FixedDatum.controlParameters.placeMulEquiv FixedDatum.controlDatum.towerExp v.val
  inj' _ _ h := Subtype.ext
    ((FixedDatum.controlParameters.placeMulEquiv FixedDatum.controlDatum.towerExp).injective h)

theorem actual_label_modulus (v : FixedDatum.controlDatum.bPlaces) :
    ZMod.unitsMap (FixedDatum.controlParameters.q₀.dvd_mul_right
      (towerDeg FixedDatum.controlDatum.towerExp)) (actual_labels v) = -1 :=
  FixedDatum.controlDatum.placeClass_of_mem_bPlaces v.val v.property

end
end SelectedPlace
#print axioms SelectedPlace.actual_selected
#print axioms SelectedPlace.selected_large
#print axioms SelectedPlace.actual_label_modulus
