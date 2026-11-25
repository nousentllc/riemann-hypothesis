import ReciprocityTheory.Chebotarev.EulerSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.Primes
theorem summable_one_div_absNorm_sq :
    ∀ (F : Type) [Field F] [NumberField F],
      Summable fun v : HeightOneSpectrum (𝓞 F) => 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro F _ _
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F (s := 2) (by norm_num)).comp_injective
    (i := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)
  refine h.congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_num

end GlobalTheory.CompanionTheory.SW.Primes
namespace GlobalTheory.CompanionTheory.SW.Growth
variable {F : Type} [Field F] [NumberField F]
theorem two_le_norm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega
theorem exists_exponents (a : ℕ) (ha : 0 < a) :
    ∃ e : HeightOneSpectrum (𝓞 F) → ℕ,
      (∀ v, Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e v ∧ ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e v + 1)) ∧
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ∧
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℝ)) ^ e v = (a : ℝ) ^ Module.finrank ℚ F := by
  set I : Ideal (𝓞 F) := Ideal.span {(a : 𝓞 F)} with hI
  have hI0 : I ≠ 0 := by
    rw [hI]; simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast ha.ne'
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hf := Ideal.hasFiniteMulSupport hI0
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    exact map_finprod φ hf
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    intro v; rw [HeightOneSpectrum.maxPowDividing, map_pow]; rfl
  refine ⟨fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors, fun v => ⟨?_, ?_⟩, ?_, ?_⟩
  · have h := finprod_mem_dvd v hf
    rw [Ideal.finprod_heightOneSpectrum_factorization hI0] at h
    exact Ideal.le_of_dvd h
  · intro h
    refine Ideal.finprod_not_dvd v I hI0 ?_
    rw [Ideal.finprod_heightOneSpectrum_factorization hI0]
    exact Ideal.dvd_iff_le.2 h
  · have h2 := hf.fun_comp (g := φ) (map_one φ)
    simpa only [Function.comp_def, hval] using h2
  · simp only [← hval]
    rw [← h1]
    change ((Ideal.absNorm I : ℕ) : ℝ) = _
    rw [hI, Ideal.absNorm_span_singleton]
    have h3 : (a : 𝓞 F) = algebraMap ℤ (𝓞 F) (a : ℤ) := by simp
    rw [h3, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
    push_cast; rfl

theorem exists_den (β : F) : ∃ D : ℕ, 0 < D ∧ ∃ x : 𝓞 F, (D : F) * β = algebraMap (𝓞 F) F x := by
  have halg : IsAlgebraic ℤ β :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic β)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  let x' : 𝓞 F := ⟨y • β, hy⟩
  have hx' : algebraMap (𝓞 F) F x' = (y : F) * β := by
    change y • β = _
    rw [zsmul_eq_mul]
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨x', ?_⟩
    rw [hx']
    conv_rhs => rw [h1]
    simp
  · refine ⟨-x', ?_⟩
    rw [map_neg, hx']
    conv_rhs => rw [h1]
    simp
end GlobalTheory.CompanionTheory.SW.Growth
namespace DensityReplay
theorem bound_step {q : ℝ} {M : ℕ} (hq : 2 ≤ q) (hM : 3 ≤ M) {Dp D' : ℝ}
    (hD' : |D' - 1| ≤ 2 / q ^ (M - 1))
    (hDp : |Dp - 1| ≤ 1 / q ^ (M - 1) + 1 / q ^ (2 * M - 1)) :
    |Dp + q ^ 2 / q ^ (2 * M) * D' - 1| ≤ 2 / q ^ (M - 1) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : 2 * (k + 3) - 1 = 2 * (k + 2) + 1 := by omega
  have e3 : 2 * (k + 3) = 2 * (k + 2) + 2 := by omega
  rw [e1] at hD' hDp ⊢
  rw [e2] at hDp
  rw [e3]
  have f1 : q ^ (2 * (k + 2) + 1) = (q ^ (k + 2)) ^ 2 * q := by rw [pow_succ, pow_mul']
  have f2 : q ^ (2 * (k + 2) + 2) = (q ^ (k + 2)) ^ 2 * q ^ 2 := by rw [pow_add, pow_mul']
  rw [f1] at hDp
  rw [f2]
  have ht4 : 4 ≤ q ^ (k + 2) := by
    have h1 : q ^ 2 ≤ q ^ (k + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith
  generalize q ^ (k + 2) = t at ht4 hD' hDp ⊢
  have htpos : 0 < t := by linarith
  have hqr : q ^ 2 / (t ^ 2 * q ^ 2) * D' = (1 / t) ^ 2 * D' := by
    field_simp
  have hf1 : 1 / (t ^ 2 * q) = (1 / t) ^ 2 * (1 / q) := by field_simp
  have hf2 : 2 / t = 2 * (1 / t) := by ring
  rw [hqr, hf2]
  rw [hf2] at hD'
  rw [hf1] at hDp
  have hu0 : 0 < 1 / t := by positivity
  have hu4 : 1 / t ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ht4
  have hr0 : 0 < 1 / q := by positivity
  have hr2 : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  generalize 1 / t = u at hu0 hu4 hD' hDp ⊢
  generalize 1 / q = r at hr0 hr2 hDp
  rw [abs_le] at hD' hDp ⊢
  obtain ⟨hb1, hb2⟩ := hD'
  obtain ⟨ha1, ha2⟩ := hDp
  have p1 := mul_le_mul_of_nonneg_left hb2 (sq_nonneg u)
  have p2 := mul_le_mul_of_nonneg_left hb1 (sq_nonneg u)
  have p3 := mul_le_mul_of_nonneg_left hr2 (sq_nonneg u)
  have p4 := mul_le_mul_of_nonneg_left hu4 hu0.le
  have p5 := mul_le_mul_of_nonneg_left hu4 (sq_nonneg u)
  have p6 := mul_nonneg (sq_nonneg u) hr0.le
  constructor <;> nlinarith

end DensityReplay
