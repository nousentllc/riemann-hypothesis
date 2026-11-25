import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
open GlobalTheory.CompanionTheory.SW.Growth
namespace ProgressionGrowth

theorem lower_product {F : Type} [Field F] [NumberField F]
    (B : Finset (HeightOneSpectrum (𝓞 F)))
    (u : ℕ → HeightOneSpectrum (𝓞 F) → ℝ) (base : HeightOneSpectrum (𝓞 F) → ℝ)
    (hbad : ∀ j v, v ∈ B → base v ≤ u j v)
    (hpos : ∀ v ∈ B, 0 < base v)
    (hgood : ∀ j v, v ∉ B →
      |u j v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    (hsum : ∀ j, Summable fun v => |u j v - 1|) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ j, κ ≤ ∏' v, u j v := by
  classical
  let V := {v : HeightOneSpectrum (𝓞 F) // v ∉ B}
  let d : V → ℝ := fun v => 2 / (Ideal.absNorm v.1.asIdeal : ℝ) ^ 2
  have hd : Summable d := by
    have h := ((Primes.summable_one_div_absNorm_sq F).mul_left 2).comp_injective
      (i := fun v : V => v.1) Subtype.val_injective
    exact h.congr fun v => by simp [d, Function.comp_apply, div_eq_mul_inv]
  have hd0 (v : V) : 0 ≤ d v := by dsimp [d]; positivity
  have hd1 (v : V) : d v < 1 := by
    have hq : (2 : ℝ) ≤ Ideal.absNorm v.1.asIdeal := by exact_mod_cast Growth.two_le_norm v.1
    dsimp [d]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hs : Summable fun v : V => |(1 - d v) - 1| := hd.congr fun v => by
    rw [show 1 - d v - 1 = -(d v) by ring, abs_neg, abs_of_nonneg (hd0 v)]
  have low := AbsTprod.abs_tprod V (fun v => 1 - d v) hs
  let K := ∏' v : V, (1 - d v)
  have hK : 0 < K := low.2.2.1 fun v => sub_pos.mpr (hd1 v)
  refine ⟨(∏ v ∈ B, base v) * K, mul_pos (Finset.prod_pos hpos) hK, ?_⟩
  intro j
  obtain ⟨hm, hspl⟩ := (AbsTprod.abs_tprod _ _ (hsum j)).2.1 B
  rw [hspl]
  apply mul_le_mul (Finset.prod_le_prod (fun v hv => (hpos v hv).le) (hbad j)) _ hK.le
    (Finset.prod_nonneg (fun v hv => (hpos v hv).le.trans (hbad j v hv)))
  apply le_of_tendsto_of_tendsto' low.1.hasProd hm.hasProd
  intro T
  apply Finset.prod_le_prod (fun v _ => (sub_pos.mpr (hd1 v)).le)
  intro v _
  have h := (abs_le.mp (hgood j v.1 v.2)).1
  change 1 - 2 / (Ideal.absNorm v.1.asIdeal : ℝ)^2 ≤ u j v.1
  linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}

theorem progression_growth (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (β : F) (hβ : β ≠ 0) (hne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) :
    ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧ ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ,
      let a := N * (1 + Q*j)
      c * (a : ℝ) ^ (Module.finrank ℚ F * (2*M-2)) ≤
        ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v a)).toReal := by
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
  set Q := ∏ v ∈ B, Ideal.absNorm v.asIdeal with hQdef
  have hQ : 0 < Q := Finset.prod_pos fun v _ => by have := two_le_norm v; omega

  have hunit (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ B) (j : ℕ) :
      ((1 + Q*j : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    have hQm : (Q : 𝓞 F) ∈ v.asIdeal := by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv
      rw [hQdef, hc]; push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    intro h
    have h1 := v.asIdeal.sub_mem h (v.asIdeal.mul_mem_right (j : 𝓞 F) hQm)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using h1))
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
  let A : ℕ → ℕ := fun j => N*(1+Q*j)
  have hA (j : ℕ) : 0 < A j := by dsimp [A]; positivity
  let u (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) := (mL σ b m ((A j : F)^2 * β) v).toReal
  have hfixed (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ B) :
      (mL σ b m ((N : F)^2 * β) v).toReal ≤ u j v := by
    let t := 1+Q*j
    have ht : 0 < t := by dsimp [t]; omega
    have htunit : (t : 𝓞 F) ∉ v.asIdeal := hunit v hv j
    have h := dil_eq (b := b) hσ hJ hM hlam hm v ((N : F)^2 * β) t 0 ht (by simp)
      (by simpa using fun h' => htunit ((Ideal.span_singleton_le_iff_mem _).1 h'))
    rw [dilSet_unit b v htunit] at h
    simp only [zero_mul,pow_zero,one_mul] at h
    have eqn : (A j : F)^2*β = (t:F)^2*((N:F)^2*β) := by dsimp [A,t]; push_cast; ring
    exact le_of_eq (by dsimp [u]; rw [eqn]; exact congrArg ENNReal.toReal h)
  have hsafe (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ B) :
      |u j v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ)^2 :=
    hBg v hv _ (hint (A j) (hDN.mul_right _) v) ((map_ne_zero _).2 (hβF (A j) (hA j)))
  obtain ⟨c,hc,hlow⟩ := lower_product B u _ hfixed hpos hsafe (fun j => (hfin (A j) (hA j)).2)
  refine ⟨N,Q,hN,hQ,c,hc,?_⟩
  intro j
  let a := A j
  have ha : 0 < a := hA j
  change c * (a : ℝ)^_ ≤ ∏' v, (m v _ (dilSet b v a)).toReal
  have hw := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ (fun v => (mL σ b m ((a : F) ^ 2 * β) v).toReal) (hfin a ha).2
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

  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hlow j) (by positivity)
end ProgressionGrowth
#print axioms ProgressionGrowth.progression_growth
