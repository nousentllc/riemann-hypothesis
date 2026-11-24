import OriginalSlices
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import ReciprocityTheory.Chebotarev.EulerSum

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Filter
open scoped TensorProduct Matrix Topology Classical

namespace PositivityTheory.SiegelWeilFormula.Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def eSp (v : HeightOneSpectrum (𝓞 F)) : ℂ := if IsField (Fv F v ⊗[F] E) then -1 else 1

def LOrd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ), ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H j ∧ ∀ᶠ s in 𝓝[≠] (j : ℂ), H s =
      (s - j) ^ (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1 else Module.finrank ℚ F) * Z s

end PositivityTheory.SiegelWeilFormula.Gen
namespace PositivityTheory.SiegelWeilFormula.Gen.W

theorem unr_prod {F : Type} [Field F] [NumberField F] (n M : ℕ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (e : HeightOneSpectrum (𝓞 F) → ℤˣ) :
    ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v : ↥Sᶜ => unrP n M (e v) (Ideal.absNorm v.1.asIdeal) z) (D z) := by
  have key : ∀ i : Fin n, ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v : ↥Sᶜ => 1 - ((e v : ℤ) : ℂ) ^ (M + (i : ℕ)) * (Ideal.absNorm v.1.asIdeal : ℂ) ^
        (-(2 * z + n - (i : ℕ)))) (d z) := by
    intro i
    obtain ⟨d, hd, hp⟩ := euler_prod (ι := ↥Sᶜ) (fun v => Ideal.absNorm v.1.asIdeal)
      (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
      (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
        (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
      (fun v => ((e v : ℤ) : ℂ) ^ (M + (i : ℕ))) (fun v => norm_unit_pow _ _) (n - 1 - i)
    refine ⟨d, hd, fun z hz => ?_⟩
    convert hp z hz using 4 with v
    have hi : (n - 1 - (i : ℕ) + 1 : ℕ) = n - i := by omega
    rw [hi, Nat.cast_sub i.2.le]
    ring_nf
  choose d hd hp using key
  refine ⟨fun z => ∏ i, d i z, DifferentiableOn.fun_finsetProd fun i _ => hd i, fun z hz => ?_⟩
  exact hasProd_prod fun i _ => hp i z hz

theorem exists_finset_of_cofinite {α : Type} {p : α → Prop} (h : ∀ᶠ v in Filter.cofinite, p v) :
    ∃ S : Finset α, ∀ v, v ∉ S → p v := by
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv ((Set.Finite.mem_toFinset _).2 h')

end PositivityTheory.SiegelWeilFormula.Gen.W

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ
open PositivityTheory.SiegelWeilFormula.Gen.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSp_sq (v : HeightOneSpectrum (𝓞 F)) : eSp E v ^ 2 = 1 := by
  unfold eSp; split_ifs <;> norm_num

theorem norm_eSp (v : HeightOneSpectrum (𝓞 F)) : ‖eSp E v‖ = 1 := by
  unfold eSp; split_ifs <;> simp

theorem eSp_pow_sub (v : HeightOneSpectrum (𝓞 F)) (N i : ℕ) (hi : i ≤ N) :
    eSp E v ^ (N + i) = eSp E v ^ (((N - i : ℕ) : ℤ)) := by
  rw [zpow_natCast]
  have : N + i = (N - i) + 2 * i := by omega
  rw [this, pow_add, pow_mul, eSp_sq, one_pow, mul_one]

theorem one_sub_eSp_ne (v : HeightOneSpectrum (𝓞 F)) :
    1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  intro h
  have h1 : eSp E v / (Ideal.absNorm v.asIdeal : ℂ) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_div, norm_eSp, Complex.norm_natCast, norm_one] at h2
  have : (1 : ℝ) / Ideal.absNorm v.asIdeal < 1 := by rw [div_lt_one (by linarith)]; exact hq
  linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_gt (S : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - c v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (j : ℂ) (hj : 1 < j.re) (hH : AnalyticAt ℂ H j) (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) : H j = Z j := by
  obtain ⟨d, hd, hdp⟩ := euler_prod (ι := {v // v ∉ S}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => c v.1) (fun v => hc v.1) 0
  have hZd : ∀ s : ℂ, 1 < s.re → Z s = d ((s - 1) / 2) := by
    intro s hs
    have h1 : 0 < ((s - 1) / 2).re := by simp; linarith
    refine (hp s hs).unique ?_
    convert hdp _ h1 using 3 with v
    push_cast
    ring_nf
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcd : ContinuousAt (fun s : ℂ => d ((s - 1) / 2)) j := by
    have h1 : 0 < ((j - 1) / 2).re := by simp; linarith
    have hdo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have := (hd.differentiableAt (hdo.mem_nhds h1)).continuousAt
    exact ContinuousAt.comp (g := d) (f := fun s : ℂ => (s - 1) / 2) this
      ((continuous_id.sub continuous_const).div_const 2).continuousAt
  have hev : H =ᶠ[𝓝[≠] j] fun s => d ((s - 1) / 2) := by
    filter_upwards [he, nhdsWithin_le_nhds (ho.mem_nhds hj)] with s hs hs'
    rw [hs, hZd s hs']
  have t1 : Tendsto H (𝓝[≠] j) (𝓝 (H j)) := hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto H (𝓝[≠] j) (𝓝 (d ((j - 1) / 2))) :=
    (hcd.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  rw [tendsto_nhds_unique t1 t2, hZd j hj]

theorem lam_tendsto (S : Finset (HeightOneSpectrum (𝓞 F))) (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (hH : AnalyticAt ℂ H 1) (he : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H s = Z s) :
    Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 ((∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H 1)) := by
  have hofR : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp))
      (eventually_nhdsWithin_of_forall fun s hs => ?_)
    show (s : ℂ) ≠ 1
    exact_mod_cast ne_of_gt (show (1 : ℝ) < s from hs)
  have hH1 : Tendsto (fun s : ℝ => H s) (𝓝[>] 1) (𝓝 (H 1)) :=
    (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hofR
  have hfin : Tendsto (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 (∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)))) := by
    have hc : Continuous (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) := by
      refine continuous_finsetProd S fun v _ => continuous_const.sub (continuous_const.mul ?_)
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v
        exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
      exact Continuous.const_cpow (Complex.continuous_ofReal.neg) (Or.inl hq)
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    convert this using 2
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Complex.cpow_neg_one, div_eq_mul_inv]
  refine (hfin.mul hH1).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hofR.eventually he] with s hs hs'
  have hs1 : 1 < ((s : ℂ)).re := by simpa using hs
  rw [((hasProd_split' (fun v => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) S _
    (hp s hs1)).tprod_eq), hs']

theorem lpack (hLO : LOrd) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℂ → ℂ, MeromorphicOn K Set.univ ∧ AnalyticAt ℂ K 0 ∧
      (∀ z : ℂ, 0 < z.re →
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) z) (K z)) ∧
      ∃ lam P : ℂ,
        Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1) (𝓝 lam) ∧
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) P ∧
        K 0 * ∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) = lam * P := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  choose Z hZm hZp H hHa hHe using fun i : Fin (m + 1) => hLO F E σ hcm S (((m + 1 - i : ℕ)) : ℤ)
  have hj1 : ∀ i : Fin (m + 1), 1 ≤ m + 1 - (i : ℕ) := fun i => by omega
  have hHe' : ∀ i : Fin (m + 1), ∀ᶠ s in 𝓝[≠] (((m + 1 - i : ℕ) : ℂ)), H i s = Z i s := by
    intro i
    have h := hHe i
    rw [if_pos (by exact_mod_cast hj1 i)] at h
    simpa only [pow_zero, one_mul, Int.cast_natCast] using h
  have hHa' : ∀ i : Fin (m + 1), AnalyticAt ℂ (H i) ((m + 1 - i : ℕ) : ℂ) := fun i => by
    simpa only [Int.cast_natCast] using hHa i
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Fin (m + 1) → ℂ → ℂ,
      Zc = fun i => Function.update (Z i) ((m + 1 - i : ℕ) : ℂ) (H i ((m + 1 - i : ℕ) : ℂ)) := ⟨_, rfl⟩
  have hfix : ∀ i : Fin (m + 1), MeromorphicOn (Zc i) Set.univ ∧ AnalyticAt ℂ (Zc i) ((m + 1 - i : ℕ) : ℂ) ∧
      Zc i ((m + 1 - i : ℕ) : ℂ) = H i ((m + 1 - i : ℕ) : ℂ) ∧
      ∀ s, s ≠ ((m + 1 - i : ℕ) : ℂ) → Zc i s = Z i s := fun i => by
    subst hZc
    exact fix_point (Z i) (H i) _ (hZm i) (hHa' i) (hHe' i)
  have h0 : ∀ i : Fin (m + 1), (2 * (0 : ℂ) + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) = ((m + 1 - i : ℕ) : ℂ) := fun i => by
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    ring
  have hqne : ∀ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hnc : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ), ‖eSp E v ^ k‖ ≤ 1 := fun v k => by
    rw [norm_zpow, norm_eSp, one_zpow]
  refine ⟨fun z => ∏ i : Fin (m + 1), Zc i (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)), ?_, ?_, ?_, ?_⟩
  · intro z _
    exact MeromorphicAt.fun_prod fun i _ => ((hfix i).1 _ trivial).comp_analyticAt
      (g := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop)
  · refine (Finset.analyticAt_prod (Finset.univ : Finset (Fin (m + 1))) fun i _ =>
      AnalyticAt.comp_of_eq (hfix i).2.1
      (f := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop) (h0 i)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp [Finset.prod_apply]
  · intro z hz
    unfold unrX
    refine hasProd_prod fun i _ => ?_
    have hi : (i : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast i.2
    have hre : 1 < (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat]
      push_cast at hi ⊢
      nlinarith
    have hne : 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ) ≠ ((m + 1 - i : ℕ) : ℂ) := by
      intro h
      have h' := congrArg Complex.re h
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)] at h'
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat] at h'
      push_cast at h'
      nlinarith
    rw [(hfix i).2.2.2 _ hne]
    convert hZp i _ hre using 2 with v
    rw [pow_sub_of_sq _ (eSp_sq v.1) (m + 1) i (by omega)]
  ·
    have hlj : ((m + 1 - ((Fin.last m : Fin (m + 1)) : ℕ) : ℕ) : ℂ) = 1 := by simp
    have hZl : ∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z (Fin.last m) s) := fun s hs => by
      convert hZp (Fin.last m) s hs using 2 with v
      simp
    have hHl : AnalyticAt ℂ (H (Fin.last m)) 1 := hlj ▸ hHa' (Fin.last m)
    have hEl : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H (Fin.last m) s = Z (Fin.last m) s := hlj ▸ hHe' (Fin.last m)
    refine ⟨(∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H (Fin.last m) 1,
      ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ), lam_tendsto S _ _ hZl hHl hEl, ?_, ?_⟩
    · have hfun : (fun v : {v // v ∉ S} => unrX (m + 1) (m + 1) (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) = fun v => ∏ i : Fin m,
            (1 - eSp E v.1 ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) *
              (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
        funext v
        exact unrX_zero_split m _ (eSp_sq v.1) _ (one_sub_eSp_ne v.1)
      rw [hfun]
      refine hasProd_prod fun i _ => ?_
      have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
        rw [Complex.natCast_re]
        have : 2 ≤ m + 1 - (i : ℕ) := by omega
        exact_mod_cast this
      exact hZp i.castSucc _ hre
    · show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) * _ = _
      rw [show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) =
          ∏ i : Fin (m + 1), H i ((m + 1 - i : ℕ) : ℂ) from
        Finset.prod_congr rfl fun i _ => by rw [h0 i]; exact (hfix i).2.2.1]
      rw [Fin.prod_univ_castSucc, hlj]
      rw [show (∏ i : Fin m, H i.castSucc ((m + 1 - (i.castSucc : ℕ) : ℕ) : ℂ)) =
          ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ) from Finset.prod_congr rfl fun i _ => by
        have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
          rw [Complex.natCast_re]
          have : 2 ≤ m + 1 - (i : ℕ) := by omega
          exact_mod_cast this
        exact val_gt S _ (fun v => hnc v _) _ _ (hZp i.castSucc) _ hre (hHa' i.castSucc) (hHe' i.castSucc)]
      ring

end PositivityTheory.SiegelWeilFormula.Gen.WQ

namespace PositivityTheory.SiegelWeilFormula.Gen.WL

theorem densZero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : M < n) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) :
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv 0 := by
  haveI : Nontrivial (Fv F v ⊗[F] E) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F
    (Fv F v) E (algebraMap F (Fv F v)).injective (algebraMap F E).injective
  refine ⟨continuousOn_const, fun S _ hS => ?_⟩
  have : gramR (Fv F v) σ J ⁻¹' (Subtype.val '' S) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun X ⟨s, hs, e⟩ => ?_
    have hu := hS hs
    simp only [Set.mem_setOf_eq] at hu
    rw [e] at hu
    let A : Matrix (Fin n) (Fin M) (Fv F v ⊗[F] E) := Matrix.of fun a i => sigR (Fv F v) σ (X a i)
    let B : Matrix (Fin M) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i b => ∑ j, JR (Fv F v) J i j * X b j
    have hg : gramR (Fv F v) σ J X = A * B := by
      ext a b
      simp only [gramR, hR, hform, Matrix.mul_apply, A, B, Matrix.of_apply, Finset.mul_sum, mul_assoc]
    rw [hg, det_mul_eq_zero_of_lt h] at hu
    exact not_isUnit_zero hu
  simp [this]

theorem eSp_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (M i : ℕ) : eSp E v ^ (M + i) = eSp E v ^ ((M : ℤ) - (i : ℕ)) := by
  unfold eSp
  split_ifs
  · rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, pow_add]
    rcases neg_one_pow_eq_or ℂ i with h | h <;> simp [h, div_neg]
  · simp

theorem hasProd_split' {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : {v // v ∉ S} => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) :=
  PositivityTheory.SiegelWeilFormula.Gen.W.hasProd_split f S D h

end PositivityTheory.SiegelWeilFormula.Gen.WL
end
