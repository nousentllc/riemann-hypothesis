import ReadableDatum

open New
noncomputable section
namespace FixedDatum

/-- A necessary lower bound from the scale fields alone. -/
theorem scale_floor {P : Parameters} (D : Data P) : 2 ^ 100 < D.natX := by
  obtain ⟨e, -, hs⟩ := D.exists_m_eq_two_pow
  have he : 22 ≤ D.towerExp := by omega
  have he' : (22 : ℝ) ≤ D.towerExp := by exact_mod_cast he
  have hx := D.towerExp_le
  have hb : (3 : ℝ) < D.logB := by
    linarith [D.logX_le_logX₁, D.logX₁_le_logB]
  have hl : 1 < Real.log D.logB :=
    (Real.lt_log_iff_exp_lt (by linarith)).2 (Real.exp_one_lt_three.trans hb)
  have hx100 : 100 ≤ D.logX := by linarith [D.mul_log_logB_le_logX]
  have hpow : (2 : ℝ) ^ 100 < Real.exp 1 ^ 100 :=
    pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
  have heq : Real.exp 1 ^ 100 = Real.exp 100 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [heq] at hpow
  have hf := hpow.trans_le (Real.exp_le_exp.mpr hx100)
  rw [D.exp_logX] at hf
  exact_mod_cast hf

theorem no_datum_at_400001 (P : Parameters) : ¬ Realized P 400001 := by
  rintro ⟨D,h⟩
  have hf := scale_floor D
  rw [h] at hf
  norm_num at hf

/-- Neither distinguished readable level prime can play the old auxiliary prime. -/
theorem level_prime_residue {P : Parameters} (D : Data P) (i : Fin 2) :
    D.levelPrime i % 8 = 1 := by
  have h₈ : 8 ∣ P.q₀ := (by decide : 8 ∣ 18480).trans P.dvd_q₀
  have hbase : 8 ∣ P.q₀ * P.d := h₈.trans (dvd_mul_right _ _)
  have hq₂ : 8 ∣ P.q₂ D.towerExp := hbase.trans (dvd_pow_self _ (by omega))
  have hd : 8 ∣ P.q₂ D.towerExp ^ 2 := hq₂.trans (dvd_pow_self _ (by decide))
  exact (D.levelPrime_modEq_one_q₂_sq i).of_dvd hd

end FixedDatum
#print axioms FixedDatum.scale_floor
#print axioms FixedDatum.no_datum_at_400001
#print axioms FixedDatum.level_prime_residue
