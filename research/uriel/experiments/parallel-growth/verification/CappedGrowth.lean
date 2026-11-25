import ExceptionalDilation
import ProgressionGrowth

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace CappedGrowth

/-- The exact order at an exceptional place is at most the prescribed cap.
Written with the same two ideal-power conditions as the original scaling theorem. -/
def WithinCap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (t H : ℕ) : Prop :=
  ∃ e : ℕ, e ≤ H ∧ Ideal.span {(t : 𝓞 F)} ≤ v.asIdeal^e ∧
    ¬ Ideal.span {(t : 𝓞 F)} ≤ v.asIdeal^(e+1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}

theorem bounded_order_growth (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))
    (β : F) (hβ : β ≠ 0) (hne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) :
    ∃ (N : ℕ) (B : Finset (HeightOneSpectrum (𝓞 F))), 0 < N ∧
      ∀ H : HeightOneSpectrum (𝓞 F) → ℕ, ∃ c : ℝ, 0 < c ∧
        ∀ t : ℕ, 0<t → (∀ v∈B, WithinCap v t (H v)) →
          let a := N*t
          c*(a:ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤
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

  refine ⟨N,B,hN,fun H => ?_⟩
  let good (t : ℕ) := 0<t ∧ ∀ v∈B, WithinCap v t (H v)
  have g1 : good 1 := by
    refine ⟨by decide,fun v _ => ⟨0,Nat.zero_le _,by simp,?_⟩⟩
    simpa using v.isPrime.ne_top
  let f (t : ℕ) := if good t then t else 1
  have hf (j : ℕ) : good (f j) := by
    by_cases hj : good j
    · simpa [f,hj] using hj
    · simpa [f,hj] using g1
  let A (j : ℕ) := N*f j
  have hA (j : ℕ) : 0 < A j := Nat.mul_pos hN (hf j).1
  let u (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) := (mL σ b m ((A j : F)^2*β) v).toReal
  let base (v : HeightOneSpectrum (𝓞 F)) :=
    (mL σ b m ((N : F)^2*β) v).toReal / (Ideal.absNorm v.asIdeal : ℝ)^(H v*(2*M-2))
  have hbase (v : HeightOneSpectrum (𝓞 F)) (hv : v∈B) : 0 < base v := by
    have hq : (0:ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (by have := two_le_norm v; omega : 0 < Ideal.absNorm v.asIdeal)
    exact div_pos (hpos v hv) (pow_pos hq _)
  have hfixed (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : v∈B) : base v ≤ u j v := by
    obtain ⟨e,he,h₁,h₂⟩ := (hf j).2 v hv
    have h := ExceptionalDilation.lower_of_bounded_order (b := b) hσ hJ hM hlam hm v
      ((N:F)^2*β) (hβF N hN) (f j) e (H v) (hf j).1 he h₁ h₂
    have eqn : (A j:F)^2*β = (f j:F)^2*((N:F)^2*β) := by dsimp [A]; push_cast; ring
    simpa only [base,u,eqn] using h
  have hsafe (j : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ B) :
      |u j v - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ)^2 :=
    hBg v hv _ (hint (A j) (hDN.mul_right _) v) ((map_ne_zero _).2 (hβF (A j) (hA j)))
  obtain ⟨c,hc,hlow⟩ := ProgressionGrowth.lower_product B u base hfixed hbase hsafe
    (fun j => (hfin (A j) (hA j)).2)
  refine ⟨c,hc,fun t ht hcap => ?_⟩
  have htgood : good t := ⟨ht,hcap⟩
  have hft : f t = t := if_pos htgood
  let a := A t
  have ha : 0 < a := hA t
  have eqn : N*t=a := by dsimp [a,A]; rw [hft]
  change c * ((N*t:ℕ):ℝ)^_ ≤ ∏' v, (m v _ (dilSet b v (N*t))).toReal
  rw [eqn]
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
  exact mul_le_mul_of_nonneg_left (hlow t) (by positivity)
end CappedGrowth
#print axioms CappedGrowth.bounded_order_growth
