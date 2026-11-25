import PrimeBlocks
import GrowthSandwich
import ExceptionalDilation

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace ExceptionalPrimeCriterion

def rationalPrime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (v.asIdeal.under ℤ).absNorm

theorem prime_below {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (rationalPrime v).Prime := by
  let _ : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact Nat.absNorm_under_prime v.asIdeal

theorem integer_unit {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ) :
    (t : 𝓞 F) ∉ v.asIdeal ↔ ¬ rationalPrime v ∣ t := by
  rw [← Int.cast_natCast,Int.cast_mem_ideal_iff,Int.natCast_dvd_natCast]; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}

/-- Remove the part of t prime to the residue characteristic from the exact original mL. -/
theorem reduce_to_prime_power (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (v : HeightOneSpectrum (𝓞 F)) (s : F) (t : ℕ) (ht : 0 < t) :
    mL σ b m ((t:F)^2*s) v =
    mL σ b m (((rationalPrime v ^ (t.factorization (rationalPrime v)) : ℕ):F)^2*s) v := by
  let p := rationalPrime v
  let a := p^(t.factorization p)
  let u := t / a
  have ha : 0 < a := pow_pos (prime_below v).pos _
  have htu : a*u=t := Nat.ordProj_mul_ordCompl_eq_self t p
  have hu : 0 < u := Nat.ordCompl_pos p ht.ne'
  have hunit : (u : 𝓞 F) ∉ v.asIdeal := (integer_unit v u).mpr (Nat.not_dvd_ordCompl (prime_below v) ht.ne')
  have h := dil_eq (b := b) hσ hJ hM hlam hm v ((a:F)^2*s) u 0 hu (by simp)
    (by simpa using fun h' => hunit ((Ideal.span_singleton_le_iff_mem _).1 h'))
  rw [dilSet_unit b v hunit] at h
  simp only [zero_mul, pow_zero, one_mul] at h
  have he : (t:F)^2*s = (u:F)^2*((a:F)^2*s) := by rw [← htu]; push_cast; ring
  change mL σ b m ((t:F)^2*s) v = mL σ b m ((a:F)^2*s) v
  rw [he]
  exact h.symm

/-- The exact actual exceptional block for p at p-power shell k. All targets remain nonzero
when used in the theorem. The base N enters before the moving multiplier. -/
def blockMass (B : Finset (HeightOneSpectrum (𝓞 F))) (σ : E →ₐ[F] E)
    (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (N : ℕ) (β : F) (p k : ℕ) : ℝ :=
  ∏ v ∈ B with rationalPrime v = p, (mL σ b m (((p^k:ℕ):F)^2*((N:F)^2*β)) v).toReal

/-- Exact necessary and sufficient criterion, with original measure and dilation types.
The finite exceptional set and positive base integer are chosen before any tail floors. -/
theorem uncapped_iff (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (β : F) (hβ : β ≠ 0) (hne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) :
    ∃ (N : ℕ) (B : Finset (HeightOneSpectrum (𝓞 F))), 0 < N ∧
    ((∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 0<t →
      c*((N*t:ℕ):ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤
        ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v (N*t))).toReal) ↔
      ∀ p ∈ B.image rationalPrime, ∃ K : ℕ, ∃ d : ℝ, 0 < d ∧
        ∀ k ≥ K, d ≤ blockMass B σ b m N β p k) := by
  classical
  -- Choose the exceptional places for the full summable estimate.
  have hgood := GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b
  let B := (Filter.eventually_cofinite.1 hgood).toFinset
  have hBg (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ B) (s : Fv F v)
      (hs : s ∈ v.adicCompletionIntegers F) (hs0 : s ≠ 0) :
      |(m v (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤
        2 / (Ideal.absNorm v.asIdeal : ℝ)^2 := by
    simp only [B,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] at hv
    have hfull := hv (lam v) (hlam v) (m v) (hm v) s hs hs0
    have hq : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast two_le_norm v
    have hqpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by linarith
    apply le_trans hfull
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply pow_le_pow_right₀ _ (by omega : 2 ≤ M-1)
    linarith
  choose nv hnv0 hnv using fun v => exists_pos_mass b v _ (hne v)
  obtain ⟨D₀, hD₀, x, hx⟩ := exists_den β
  set N := D₀ * ∏ v ∈ B, nv v with hNdef
  have hN : 0 < N := Nat.mul_pos hD₀ (Finset.prod_pos fun v _ => hnv0 v)
  have hβF : ∀ n : ℕ, 0 < n → (n : F) ^ 2 * β ≠ 0 := fun n hn =>
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn.ne')) hβ
  have hint : ∀ n : ℕ, D₀ ∣ n → ∀ v, algebraMap F (Fv F v) ((n : F) ^ 2 * β) ∈ v.adicCompletionIntegers F := by
    rintro n ⟨c, rfl⟩ v
    have e : (((D₀ * c : ℕ) : F)) ^ 2 * β = algebraMap (𝓞 F) F (((D₀ * c ^ 2 : ℕ) : 𝓞 F) * x) := by
      rw [map_mul, ← hx, map_natCast]; push_cast; ring
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact val_le_one v _
  have hfin := fun n (hn : 0 < n) => scal_fin (b := b) hσ hJ hM hlam hm (hβF n hn)

  have hDN : D₀ ∣ N := Dvd.intro _ rfl
  have hpos (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ B) :
      0 < (mL σ b m ((N : F)^2 * β) v).toReal := by
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) N hN
    have h := dil_eq (b := b) hσ hJ hM hlam hm v β N (e v) hN (he v).1 (he v).2
    have hnz : m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v N) ≠ 0 := by
      obtain ⟨c, hc⟩ : nv v ∣ N := (Finset.dvd_prod_of_mem nv hv).mul_left _
      intro h0
      refine hnv v (measure_mono_null ?_ h0)
      rw [hc]; exact dilSet_mono b v _ _
    have hz : mL σ b m ((N : F) ^ 2 * β) v ≠ 0 := by
      intro h0
      rw [h, h0, mul_zero] at hnz
      exact hnz rfl
    exact ENNReal.toReal_pos hz ((hfin N hN).1 v).ne


  let s := (N:F)^2*β
  let u (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) := (mL σ b m ((t:F)^2*s) v).toReal
  let f := blockMass B σ b m N β
  let P := B.image rationalPrime
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp; obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hp; exact prime_below v
  have heq (t : ℕ) : ((N*t:ℕ):F)^2*β = (t:F)^2*s := by dsimp [s]; push_cast; ring
  have hgood' (t : ℕ) (ht : 0<t) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ B) :
      |u t v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ)^2 := by
    dsimp [u]; rw [← heq]
    exact hBg v hv _ (hint (N*t) (hDN.mul_right _) v) ((map_ne_zero _).2 (hβF _ (Nat.mul_pos hN ht)))
  have hsum (t : ℕ) (ht : 0<t) : Summable fun v => |u t v - 1| := by
    dsimp [u]; rw [← heq]; exact (hfin _ (Nat.mul_pos hN ht)).2
  obtain ⟨L,U,hL,hU,hsand⟩ := GrowthSandwich.sandwich B u (fun _ _ => ENNReal.toReal_nonneg) hgood' hsum
  have hpos' (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ B) (t : ℕ) (ht : 0<t) : 0 < u t v := by
    obtain ⟨e,he,-,-⟩ := exists_exponents (F := F) t ht
    have h := ExceptionalDilation.lower_of_bounded_order (b := b) hσ hJ hM hlam hm v
      s (hβF _ hN) t (e v) (e v) ht le_rfl (he v).1 (he v).2
    have hq : (0:ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (by have := two_le_norm v; omega : 0 < Ideal.absNorm v.asIdeal)
    exact (div_pos (hpos v hv) (pow_pos hq _)).trans_le h
  have hfp (p : ℕ) (hp : p ∈ P) (k : ℕ) : 0 < f p k :=
    Finset.prod_pos fun v hv => hpos' v (Finset.mem_filter.mp hv).1 _ (pow_pos (hP p hp).pos k)
  have hgroup (t : ℕ) (ht : 0<t) :
      (∏ p ∈ P, f p (t.factorization p)) = (∏ v ∈ B, u t v) := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := B) (t := P) (g := rationalPrime)
      (fun v hv => Finset.mem_image_of_mem _ hv) (u t)]
    refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨_,hp⟩ := Finset.mem_filter.mp hv
    dsimp [u]; rw [reduce_to_prime_power (b := b) hσ hJ hM hlam hm v s t ht,hp]
  let D := Module.finrank ℚ F*(2*M-2)
  have hscale (t : ℕ) (ht : 0<t) :
      (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v (N*t))).toReal) =
      ((N*t:ℕ):ℝ)^D * ∏' v, u t v := by
    rw [GrowthSandwich.scale_product (b := b) hσ hJ hM hlam hm β hβ _ (Nat.mul_pos hN ht),heq]
  have hpow (t : ℕ) (ht : 0<t) : 0 < ((N*t:ℕ):ℝ)^D := by positivity
  refine ⟨N,B,hN,?_⟩
  rw [← PrimeBlocks.block_criterion P hP f hfp]
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨c/U,div_pos hc hU, fun t ht => ?_⟩
    have hh := h t ht
    rw [hscale t ht,mul_comm] at hh
    have small := (le_of_mul_le_mul_left hh (hpow t ht)).trans (hsand t ht).2
    rw [hgroup t ht,div_le_iff₀ hU,mul_comm]; exact small
  · rintro ⟨c,hc,h⟩
    refine ⟨L*c,mul_pos hL hc,fun t ht => ?_⟩
    have hh := h t ht
    rw [hgroup t ht] at hh
    rw [hscale t ht, mul_comm (L*c)]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hh hL.le).trans (hsand t ht).1) (hpow t ht).le

end ExceptionalPrimeCriterion
#print axioms ExceptionalPrimeCriterion.reduce_to_prime_power
#print axioms ExceptionalPrimeCriterion.uncapped_iff
