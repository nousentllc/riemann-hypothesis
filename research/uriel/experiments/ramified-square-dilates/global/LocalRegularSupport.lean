import NeighborhoodGrowth
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GlobalTheory.CompanionTheory.SW.Growth ExceptionalPrimeCriterion
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace LocalRegularSupport

/-- This argument requires just one place and every local scalar is permitted.
Only the scaling rule (available in rank ≥ 1) and the regular punctured floor
are used. The geometric construction of that floor has a different rank threshold. -/
theorem all_local_targets {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (hM : 1 ≤ M) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m)
    (hg : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 →
      δ ≤ (m (hermScal (Fv F v) σ z) (latV b v)).toReal)
    (s : Fv F v) (hs : s ≠ 0) :
    ∃ a : ℕ, 0 < a ∧ 0 < m (hermScal (Fv F v) σ s) (dilSet b v a) := by
  obtain ⟨δ,hδ,hnear⟩ := hg
  have hmem : ((rationalPrime v : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem _
  have hsmall : Valued.v ((rationalPrime v : ℕ) : Fv F v) < 1 := by simpa using val_lt_one_of_mem v hmem
  have ht : Tendsto (fun k : ℕ => (((rationalPrime v^k:ℕ):Fv F v)^2*s)) atTop (𝓝 0) := by
    simpa using ((Valued.tendsto_zero_pow_of_v_lt_one hsmall).pow 2).mul_const s
  obtain ⟨k,hk⟩ := (ht.eventually hnear).exists
  let a := rationalPrime v ^ k
  have ha : 0 < a := pow_pos (prime_below v).pos _
  have hz : (a:Fv F v)^2*s ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ha.ne' : (a:Fv F v)≠0)) hs
  have hloc : m (hermScal (Fv F v) σ ((a:Fv F v)^2*s)) (latV b v) ≠ 0 := by
    have h := hδ.trans_le (hk hz)
    intro he; rw [he,ENNReal.toReal_zero] at h; exact h.false
  obtain ⟨e,he,-,-⟩ := exists_exponents (F := F) a ha
  have hid := GlobalTheory.T.local_rank_one_density_uniformizer_power F E σ hσ M J hJ d b v lam hlam m hm hM a (e v)
    ha (he v).1 (he v).2 s (latV b v) (measurable_latV b v)
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by have := two_le_norm v; omega : Ideal.absNorm v.asIdeal ≠ 0)
  exact ⟨a,ha,bot_lt_iff_ne_bot.mpr (by rw [show m (hermScal (Fv F v) σ s) (dilSet b v a) = _ from hid]; exact mul_ne_zero (pow_ne_zero _ hq) hloc)⟩

end LocalRegularSupport
#print axioms LocalRegularSupport.all_local_targets
