import ProgressionGrowth

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GrowthSandwich

/-- For every admissible positive integer n the normalized global mass is exactly
the product of the local masses of the lattice at n²β. -/
theorem scale_product {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
    {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}
    (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (β : F) (hβ : β ≠ 0) (a : ℕ) (ha : 0 < a) :
    (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v a)).toReal) =
    (a : ℝ)^(Module.finrank ℚ F*(2*M-2)) * ∏' v, (mL σ b m ((a : F)^2*β) v).toReal := by
  have hfin := scal_fin (b := b) hσ hJ hM hlam hm (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast ha.ne' : (a:F)≠0)) hβ)
  have hw := AbsTprod.abs_tprod _ _ hfin.2
  obtain ⟨e, he, hfs, hprod⟩ := exists_exponents (F := F) a ha
  have hid : ∀ v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v a)).toReal =
      (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2) * (mL σ b m ((a : F) ^ 2 * β) v).toReal := by
    intro v
    rw [dil_eq (b := b) hσ hJ hM hlam hm v β a (e v) ha (he v).1 (he v).2, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, pow_mul]
  have hf2 : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    hfs.fun_comp (g := fun y : ℝ => y ^ (2 * M - 2)) (one_pow _)
  have hmul : Multipliable
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    (hasProd_prod_of_ne_finset_one (s := Set.Finite.toFinset hf2) (fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset hf2).2 h))).multipliable
  rw [tprod_congr hid, hmul.tprod_mul hw.1, tprod_eq_finprod hf2, ← finprod_pow hfs, hprod, ← pow_mul]

/-- Uniform positive lower and finite upper constants for the exterior Euler
factor, hence for the ratio of the full and exceptional products. -/
theorem sandwich {F : Type} [Field F] [NumberField F]
    (B : Finset (HeightOneSpectrum (𝓞 F))) (u : ℕ → HeightOneSpectrum (𝓞 F) → ℝ)
    (hpos : ∀ t v, 0 ≤ u t v)
    (hgood : ∀ t : ℕ, 0 < t → ∀ v, v ∉ B → |u t v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ)^2)
    (hsum : ∀ t : ℕ, 0 < t → Summable fun v => |u t v - 1|) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ t : ℕ, 0 < t →
      L * (∏ v ∈ B, u t v) ≤ ∏' v, u t v ∧ (∏' v, u t v) ≤ U * (∏ v ∈ B, u t v) := by
  classical
  let V := {v : HeightOneSpectrum (𝓞 F) // v ∉ B}
  let d : V → ℝ := fun v => 2 / (Ideal.absNorm v.1.asIdeal : ℝ)^2
  have hd : Summable d := by
    have h := ((Primes.summable_one_div_absNorm_sq F).mul_left 2).comp_injective
      (i := fun v : V => v.1) Subtype.val_injective
    exact h.congr fun v => by simp [d, Function.comp_apply, div_eq_mul_inv]
  have hd0 (v : V) : 0 ≤ d v := by dsimp [d]; positivity
  have hd1 (v : V) : d v < 1 := by
    have hq : (2 : ℝ) ≤ Ideal.absNorm v.1.asIdeal := by exact_mod_cast two_le_norm v.1
    dsimp [d]; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hminus := AbsTprod.abs_tprod V (fun v => 1-d v)
    (hd.congr fun v => by rw [show 1-d v-1 = -(d v) by ring,abs_neg,abs_of_nonneg (hd0 v)])
  have hplus := AbsTprod.abs_tprod V (fun v => 1+d v)
    (hd.congr fun v => by rw [show 1+d v-1 = d v by ring,abs_of_nonneg (hd0 v)])
  refine ⟨_,_,hminus.2.2.1 (fun v => sub_pos.mpr (hd1 v)),hplus.2.2.1 (fun v => by linarith [hd0 v]),?_⟩
  intro t ht
  obtain ⟨hm,hsplit⟩ := (AbsTprod.abs_tprod _ _ (hsum t ht)).2.1 B
  have nonneg := Finset.prod_nonneg (s := B) (fun v _ => hpos t v)
  rw [hsplit, mul_comm (∏ _ ∈ B, _)]
  constructor
  · apply mul_le_mul_of_nonneg_right _ nonneg
    apply le_of_tendsto_of_tendsto' hminus.1.hasProd hm.hasProd
    intro S
    exact Finset.prod_le_prod (fun v _ => (sub_pos.mpr (hd1 v)).le) (fun v _ => by
      have h := (abs_le.mp (hgood t ht v.1 v.2)).1; dsimp [d]; linarith)
  · apply mul_le_mul_of_nonneg_right _ nonneg
    apply le_of_tendsto_of_tendsto' hm.hasProd hplus.1.hasProd
    intro S
    exact Finset.prod_le_prod (fun v _ => hpos t v.1) (fun v _ => by
      have h := (abs_le.mp (hgood t ht v.1 v.2)).2; dsimp [d]; linarith)

end GrowthSandwich
#print axioms GrowthSandwich.sandwich
#print axioms GrowthSandwich.scale_product
