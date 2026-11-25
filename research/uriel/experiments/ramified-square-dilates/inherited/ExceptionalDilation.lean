import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open GlobalTheory.CompanionTheory.SW.Growth NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix
noncomputable section

namespace ExceptionalDilation

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ}
  {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}

/-- A moving local target has a uniform lower bound when the multiplier's
valuation at this place has cap H. The test set and measure are the original
ones in Growth.dil_eq. The factor is present even though the raw sets expand. -/
theorem lower_of_bounded_order (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M)
    (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M)
      (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (v : HeightOneSpectrum (𝓞 F)) (s : F) (hs : s ≠ 0) (a e H : ℕ) (ha : 0<a)
    (he : e ≤ H) (h₁ : Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal^e)
    (h₂ : ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal^(e+1)) :
    (mL σ b m s v).toReal / (Ideal.absNorm v.asIdeal : ℝ)^(H*(2*M-2)) ≤
      (mL σ b m ((a : F)^2*s) v).toReal := by
  let μ := m v (hermScal (Fv F v) σ (algebraMap F _ s))
  have hsub : (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) ⊆ dilSet b v a := by
    intro X hX
    apply (mem_dilSet b v).mpr
    intro i j k
    exact mul_mem (natCast_mem (v.adicCompletionIntegers F) a) (hX i j k)
  have hscale := dil_eq (b := b) hσ hJ hM hlam hm v s a e ha h₁ h₂
  have hn : ((a : F)^2*s) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ha.ne')) hs
  have hfinite := ((scal_fin (b := b) hσ hJ hM hlam hm hn).1 v).ne
  have hraw : μ (dilSet b v a) ≠ ⊤ := by
    dsimp [μ]; rw [hscale]; exact ENNReal.mul_ne_top (by finiteness) hfinite
  have hh := ENNReal.toReal_mono hraw (measure_mono (μ := μ) hsub)
  change (mL σ b m s v).toReal ≤ (μ (dilSet b v a)).toReal at hh
  dsimp only [μ] at hh
  rw [hscale,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast] at hh
  have hq : (2:ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_norm v
  have hp : 0 < (Ideal.absNorm v.asIdeal : ℝ)^(H*(2*M-2)) := pow_pos (by linarith) _
  rw [div_le_iff₀ hp,mul_comm]
  exact hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ))
      (Nat.mul_le_mul_right _ he)) ENNReal.toReal_nonneg)

end ExceptionalDilation

#print axioms ExceptionalDilation.lower_of_bounded_order
