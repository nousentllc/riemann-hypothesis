import ShellThreshold
import GermSupport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import OriginalFloor
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open ExceptionalPrimeCriterion Filter
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace OptimalSupport
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}



/-- Actual positive local shells form a final interval and have a uniform lower
bound there, even when the initial scalar is not represented in the unit lattice. -/
theorem local_threshold (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (β : F) (hβ : β ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ K : ℕ, ∃ b₀ : ℝ, 0<b₀ ∧
      (∀ t : ℕ, 0<t → (0 < (mL σ b m ((t:F)^2*β) v).toReal ↔ rationalPrime v ^ K ∣ t)) ∧
      ∀ t : ℕ, 0<t → rationalPrime v ^ K ∣ t → b₀ ≤ (mL σ b m ((t:F)^2*β) v).toReal := by
  let p := rationalPrime v
  let f (k : ℕ) := (mL σ b m (((p^k:ℕ):F)^2*β) v).toReal
  obtain ⟨d₀,hd₀,hg⟩ := OriginalFloor.punctured_floor σ hσ M J hJ hM d b v (lam v) (hlam v) (m v) (hm v)
  have ht : ∀ᶠ k : ℕ in atTop, d₀ ≤ f k := by
    filter_upwards [(NeighborhoodGrowth.targets_tend_to_zero v β).eventually hg] with k hk
    apply hk
    exact (map_ne_zero _).2 (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast (pow_pos (prime_below v).pos k).ne' : ((p^k:ℕ):F)≠0)) hβ)
  have hm' (k : ℕ) (hk : 0 < f k) : 0 < f (k+1) := by
    obtain ⟨e,he,-,-⟩ := exists_exponents (F := F) p (prime_below v).pos
    let s := ((p^k:ℕ):F)^2*β
    have hs : s ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (pow_pos (prime_below v).pos k).ne' : ((p^k:ℕ):F)≠0)) hβ
    have h := ExceptionalDilation.lower_of_bounded_order (b := b) hσ hJ hM hlam hm v s hs p (e v) (e v)
      (prime_below v).pos le_rfl (he v).1 (he v).2
    have hq : (0:ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (by have := two_le_norm v; omega : 0 < Ideal.absNorm v.asIdeal)
    have eqn : (p:F)^2*s = ((p^(k+1):ℕ):F)^2*β := by dsimp [s]; push_cast; rw [pow_succ (p:F)]; ring
    have h' := (div_pos hk (pow_pos hq _)).trans_le h
    simpa only [eqn,f] using h'
  obtain ⟨K,b₀,hb,he,hf⟩ := ShellThreshold.classify f hm' ⟨d₀,hd₀,ht⟩
  have heq (t : ℕ) (ht : 0<t) : (mL σ b m ((t:F)^2*β) v).toReal = f (t.factorization p) :=
    congrArg ENNReal.toReal (reduce_to_prime_power (b := b) hσ hJ hM hlam hm v β t ht)
  refine ⟨K,b₀,hb,fun t ht => ?_,fun t ht hdiv => ?_⟩
  · rw [heq t ht,he]; exact ((prime_below v).pow_dvd_iff_le_factorization ht.ne').symm
  · rw [heq t ht]; exact hf _ (((prime_below v).pow_dvd_iff_le_factorization ht.ne').mp hdiv)

/-- There exists one positive least generating multiplier for the complete positive
support. A single positive polynomial coefficient works on its entire support. -/
theorem positive_iff_multiple (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (β : F) (hβ : β ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 0<t →
      let P := ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v t)).toReal
      (0 < P ↔ N ∣ t) ∧ (N ∣ t → c*(t:ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤ P) := by
  classical
  have hdens := GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b
  have hunit := (GlobalTheory.T.integral_almost_all_places F E σ hσ d b).2 β hβ
  let B := (Filter.eventually_cofinite.1 (hdens.and hunit)).toFinset
  let u (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) := (mL σ b m ((t:F)^2*β) v).toReal
  have hreg (t : ℕ) (ht : 0<t) : (t:F)^2*β ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ht.ne' : (t:F)≠0)) hβ
  have hgood (t : ℕ) (ht : 0<t) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ B) :
      |u t v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ)^2 := by
    simp only [B,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] at hv
    have hint : algebraMap F (Fv F v) ((t:F)^2*β) ∈ v.adicCompletionIntegers F := by
      have hb : algebraMap F (Fv F v) β ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers,hv.2]
      simpa using mul_mem (pow_mem (natCast_mem (v.adicCompletionIntegers F) t) 2) hb
    have h := hv.1 (lam v) (hlam v) (m v) (hm v) _ hint ((map_ne_zero _).2 (hreg t ht))
    have hq : (2:ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast two_le_norm v
    have hq0 : (0:ℝ) < Ideal.absNorm v.asIdeal := by linarith
    apply h.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply pow_le_pow_right₀ _ (by omega : 2 ≤ M-1)
    linarith
  obtain ⟨L,U,hL,hU,hsand⟩ := GrowthSandwich.sandwich B u (fun _ _ => ENNReal.toReal_nonneg) hgood
    (fun t ht => (scal_fin (b := b) hσ hJ hM hlam hm (hreg t ht)).2)
  choose K δ hδ heq hfloor using (fun v => local_threshold (b := b) hσ hJ hM hlam hm β hβ v)
  let g (v : HeightOneSpectrum (𝓞 F)) := rationalPrime v ^ K v
  let N := B.lcm g
  have hN : 0<N := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (prime_below v).ne_zero))
  let base := ∏ v ∈ B, δ v
  have hbase : 0<base := Finset.prod_pos (fun v _ => hδ v)
  refine ⟨N,hN,L*base,mul_pos hL hbase,fun t ht => ?_⟩
  dsimp only
  rw [GrowthSandwich.scale_product (b := b) hσ hJ hM hlam hm β hβ t ht]
  let D := Module.finrank ℚ F*(2*M-2)
  have hpow : 0<(t:ℝ)^D := by positivity
  have suffices' (hh : N ∣ t) : L*base ≤ ∏' v, u t v := by
    have hb (v) (hv : v ∈ B) := hfloor v t ht (Finset.lcm_dvd_iff.mp hh v hv)
    exact (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => (hδ v).le) hb) hL.le).trans (hsand t ht).1
  refine ⟨⟨fun hp => ?_,fun hh => mul_pos hpow ((mul_pos hL hbase).trans_le (suffices' hh))⟩,fun hh => ?_⟩
  · rw [Finset.lcm_dvd_iff]
    intro v hv
    apply (heq v t ht).mp
    by_contra! hnon
    have hz : u t v = 0 := le_antisymm hnon ENNReal.toReal_nonneg
    have hzero : (∏ w ∈ B, u t w) = 0 := Finset.prod_eq_zero hv hz
    have hupper := (hsand t ht).2
    rw [hzero,mul_zero] at hupper
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hpow.le hupper)) hp
  · rw [mul_comm (L*base)]
    exact mul_le_mul_of_nonneg_left (suffices' hh) hpow.le
/-- An existentially selected support generator has a unique numerical value. -/
theorem generator_unique (S : ℕ → Prop) (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (h₁ : ∀ t : ℕ, 0<t → (S t ↔ a∣t)) (h₂ : ∀ t : ℕ, 0<t → (S t ↔ b∣t)) :
    a = b := Nat.dvd_antisymm ((h₁ b hb).mp ((h₂ b hb).mpr dvd_rfl))
      ((h₂ a ha).mp ((h₁ a ha).mpr dvd_rfl))

end OptimalSupport
#print axioms OptimalSupport.local_threshold
#print axioms OptimalSupport.positive_iff_multiple
#print axioms OptimalSupport.generator_unique
