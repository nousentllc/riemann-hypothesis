import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV

/- Source-derived supplement to 40e56bab. Original proofs of kexp, point, point2,
   final and the two field-level constructors have been adapted to consume only
   active weights. All arithmetic notions below are imported from original modules. -/
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
noncomputable section
namespace EndpointWeights

def ActiveSmall (eta : ℝ) (Exc : Finset ℕ) (t : ℕ) (x : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < t → k ∈ Exc → (k : ℝ) ≤ x ^ eta

def pointCap (C s x : ℝ) : ℝ := C * (1 + Real.log x) + 2 * Real.exp (C * x ^ s)

theorem kexpRelax (w r : ℝ) :
    ∀ (CK eps c0 x : ℝ) (e n n0 D : ℕ), 0 < CK → 0 < eps → 0 ≤ c0 → 1 ≤ x → (e : ℝ) ≤ x ^ (w * eps / CK) → n ≤ n0 →
      Real.log (2 * (D : ℝ)) ≤ c0 * x ^ (r * eps) →
        kBound CK e n D ≤ Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ ((w + r) * eps)) := by
  intro CK eps c0 x e n n0 D hCK heps hc0 hx he hn hD
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hy : 0 ≤ x ^ (w * eps / CK) := Real.rpow_nonneg hx0.le _
  have h1 : 2 * (e : ℝ) * n ≤ (2 * (n0 : ℝ)) * x ^ (w * eps / CK) := by
    have := mul_le_mul he hn' hn0 hy
    nlinarith
  have h2 : (2 * (e : ℝ) * n) ^ CK ≤ (2 * (n0 : ℝ)) ^ CK * x ^ (w * eps) := by
    calc (2 * (e : ℝ) * n) ^ CK ≤ ((2 * (n0 : ℝ)) * x ^ (w * eps / CK)) ^ CK :=
          Real.rpow_le_rpow (by positivity) h1 hCK.le
      _ = (2 * (n0 : ℝ)) ^ CK * x ^ (w * eps) := by
          rw [Real.mul_rpow (by positivity) hy, ← Real.rpow_mul hx0.le]
          congr 2
          field_simp
  have h3 : x ^ ((w + r) * eps) = x ^ (w * eps) * x ^ (r * eps) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  unfold kBound
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (2 * (e : ℝ) * n) ^ CK := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ c0 * x ^ (r * eps) := mul_nonneg hc0 (Real.rpow_nonneg hx0.le _)
  calc (2 * (e : ℝ) * n) ^ CK * Real.log (2 * (D : ℝ))
      ≤ (2 * (e : ℝ) * n) ^ CK * (c0 * x ^ (r * eps)) := mul_le_mul_of_nonneg_left hD ha
    _ ≤ ((2 * (n0 : ℝ)) ^ CK * x ^ (w * eps)) * (c0 * x ^ (r * eps)) := mul_le_mul_of_nonneg_right h2 hb
    _ = (2 * (n0 : ℝ)) ^ CK * c0 * x ^ ((w + r) * eps) := by rw [h3]; ring

theorem pointRelax (w r : ℝ) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R c : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], HasMuQ l L₀ → SecondBound l R L₀ →
      ∀ (Z : ℕ) (Exc : Finset ℕ), FirstBound l R c L₀ Z Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ →
          ∀ (eps Ct c0 x : ℝ) (n0 : ℕ), 0 < eps → 0 ≤ c0 → 1 ≤ x → 
            Module.finrank ℚ L₂ ≤ n0 → Real.log (2 * ((discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (r*eps) →
            ∀ e : ℕ, 1 ≤ e → e ≤ Z → (e : ℝ) ≤ x ^ Ct → (e ∈ Exc → (e : ℝ) ≤ x ^ (w * eps / CK)) →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
                shaInv L₁ l e ≠ ⊤ ∧ ((shaInv L₁ l e).toNat : ℝ) ≤
                  (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) +
                    2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ ((w+r)*eps)) := by
  intro CK hCK hK l R c _ L₀ _ hmu hSec Z Exc hF L₂ _ _ _ hL₂ eps Ct c0 x n0 heps hc0 hx hn hdisc e he1 heZ hex hgood m L₁ _ _ _ hL₁
  have hexp : 0 ≤ 2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ ((w+r)*eps)) := by positivity
  by_cases he : e ∈ Exc
  · have hg : (e : ℝ) ≤ x ^ (w * eps / CK) := hgood he
    obtain ⟨D⟩ := ldata_nonempty (F := L₂) (Ω := AlgebraicClosure L₂) l
    have hmu2 : HasMuQ l L₂ := by
      obtain ⟨ζ, hζ⟩ := hmu
      exact ⟨algebraMap L₀ L₂ ζ, hζ.map_of_injective (algebraMap L₀ L₂).injective⟩
    obtain ⟨hvt, hvb⟩ := klen CK hK l L₂ (AlgebraicClosure L₂) D hmu2 e he1
    have hkb := kexpRelax w r CK eps c0 x e (Module.finrank ℚ L₂) n0 (discr L₂).natAbs hCK heps hc0 hx hg hn hdisc
    have hs := hSec e he1 m L₁ hL₁ L₂ hL₂ (AlgebraicClosure L₂) D
    generalize VLen D ↑e = v at hvt hvb hs
    generalize shaInv L₁ l ↑e = s at hs ⊢
    lift v to ℕ using hvt
    have hst : s ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hs
      rw [← Nat.cast_add]
      exact ENat.natCast_ne_top _
    lift s to ℕ using hst
    have hs' : s ≤ v + R * (m - jZero l R) := by exact_mod_cast hs
    refine ⟨ENat.natCast_ne_top s, ?_⟩
    rw [ENat.toNat_natCast]
    simp only [ENat.toNat_natCast] at hvb
    have hN : s ≤ v + R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
      omega
    have hR : (s : ℝ) ≤ (v : ℝ) + (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith
  · have hb := hF.2 e he1 heZ he m L₁ hL₁
    generalize shaInv L₁ l ↑e = s at hb ⊢
    have hst : s ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hb
    lift s to ℕ using hst
    have hs' : s ≤ R * (max m (jZero l R) + c + Nat.log l Z) := by exact_mod_cast hb
    refine ⟨ENat.natCast_ne_top s, ?_⟩
    rw [ENat.toNat_natCast]
    have hN : s ≤ R * (m + jZero l R + c + Nat.log l Z) := by
      refine le_trans hs' (Nat.mul_le_mul_left _ ?_)
      omega
    have hR : (s : ℝ) ≤ (R : ℝ) * ((m : ℝ) + jZero l R + c + Nat.log l Z) := by
      exact_mod_cast hN
    linarith

theorem point2Relax (w r : ℝ) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R c1 n0 : ℕ) [Fact l.Prime] (c0 J Ct eps a : ℝ), 0 ≤ c0 → 0 < J → 0 ≤ Ct → 0 < eps →
      0 ≤ a → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀], HasMuQ l L₀ → SecondBound l R L₀ →
        ∀ (c : ℕ) (X : ℝ) (Exc : Finset ℕ), c ≤ c1 → FirstBound l R c L₀ ⌊X ^ Ct⌋₊ Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂], IsLayer l (jZero l R) L₀ L₂ → Module.finrank ℚ L₂ ≤ n0 →
          ∀ x : ℝ, 1 ≤ x → X ^ (1 / J) ≤ x → x ≤ X → 
            Real.log (2 * ((discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (r*eps) →
            ∀ e : ℕ, 1 ≤ e → (e : ℝ) ≤ x ^ Ct → (e ∈ Exc → (e : ℝ) ≤ x ^ (w * eps / CK)) →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
                (m : ℝ) ≤ a * (1 + Real.log x) →
                  shaInv L₁ l e ≠ ⊤ ∧ ((shaInv L₁ l e).toNat : ℝ) + 1 ≤ pointCap C ((w+r)*eps) x := by
  intro CK hCK hK l R c1 n0 hl c0 J Ct eps a hc0 hJ hCt heps ha
  have hA : 0 ≤ (R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1 := by positivity
  have hB : 0 ≤ (2 * (n0 : ℝ)) ^ CK * c0 := by positivity
  refine ⟨((R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * c0, by positivity, ?_⟩
  intro L₀ _ hmu hS c X Exc hc hF L₂ _ _ _ hL₂ hn x hx hXx hxX hD e he hex hG m L₁ _ _ _ hL₁ hm
  have hX : 1 ≤ X := hx.trans hxX
  have heZ : e ≤ ⌊X ^ Ct⌋₊ :=
    Nat.le_floor (hex.trans (Real.rpow_le_rpow (by linarith) hxX hCt))
  obtain ⟨h1, h2⟩ := pointRelax w r CK hCK hK l R c L₀ hmu hS _ Exc hF L₂ hL₂ eps Ct c0 x n0 heps hc0 hx hn hD
    e he heZ hex hG m L₁ hL₁
  refine ⟨h1, ?_⟩
  have hlog := UpperTheory.V.Win.logs.1 l J Ct X x hl.out.two_le hJ hCt hX hXx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcr : (c : ℝ) ≤ c1 := by exact_mod_cast hc
  have hp : 0 ≤ x ^ ((w+r)*eps) := by positivity
  have hj : (0 : ℝ) ≤ jZero l R := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hCJ : 0 ≤ 2 * Ct * J := by positivity
  have hin : (m : ℝ) + jZero l R + c + Nat.log l ⌊X ^ Ct⌋₊ ≤
      (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) * (1 + Real.log x) := by
    nlinarith [mul_nonneg hj hL, mul_nonneg hc1 hL]
  have hR' := mul_le_mul_of_nonneg_left hin hR
  have hexp : Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ ((w+r)*eps)) ≤
      Real.exp ((((R : ℝ) * (a + (jZero l R : ℝ) + c1 + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * c0) *
        x ^ ((w+r)*eps)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hp
  unfold pointCap
  have hBL : 0 ≤ (2 * (n0 : ℝ)) ^ CK * c0 * (1 + Real.log x) := by positivity
  nlinarith

theorem finalRelax (s : ℝ) :
    ∀ Ct eps C : ℝ, 0 < eps → s < 4 * eps / 5 → ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x ≥ x0, x ^ Ct * pointCap C s x ≤ Real.exp (x ^ (4 * eps / 5)) := by
  intro Ct eps C heps hs
  have hba : 0 < 4 * eps / 5 - s := by linarith
  have hb : 0 < 4 * eps / 5 := by linarith
  have E1 := ((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound
    (by norm_num : (0:ℝ) < 1 / 4)
  have E2 := (tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)
  have E3 := (tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))
  have E4 := Filter.eventually_ge_atTop (2:ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨max N 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hxa : 0 ≤ x ^ (s) := Real.rpow_nonneg hx0.le _
  have hxb : 0 ≤ x ^ (4 * eps / 5) := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ (4 * eps / 5) = x ^ (s) * x ^ (4 * eps / 5 - s) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog),
    abs_of_nonneg hxb] at h1
  have hC2 : |C| * x ^ (s) ≤ 1 / 4 * x ^ (4 * eps / 5) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h2 hxa]
  have hS : Real.log 3 + (|Ct| + |C|) * Real.log x + |C| + |C| * x ^ (s)
      ≤ x ^ (4 * eps / 5) := by linarith
  have hp1 : C * (1 + Real.log x)
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (s)) := by
    have q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have q2 : 0 ≤ |C| * x ^ (s) := mul_nonneg (abs_nonneg C) hxa
    linarith [Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (s))]
  have hp2 : Real.exp (C * x ^ (s))
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (s)) := by
    apply Real.exp_le_exp.mpr
    have q1 : C * x ^ (s) ≤ |C| * x ^ (s) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hxa
    have q2 : 0 ≤ |C| * (1 + Real.log x) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith
  have hpt : pointCap C s x
      ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (s)) := by
    show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (s)) ≤ _
    linarith
  have hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have q := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog
    linarith
  calc x ^ Ct * pointCap C s x
      ≤ x ^ Ct * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (s))) :=
        mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hx0.le _)
    _ ≤ Real.exp (|Ct| * Real.log x)
          * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (s))) :=
        mul_le_mul_of_nonneg_right hxc (by positivity)
    _ = Real.exp (|Ct| * Real.log x + Real.log 3
          + (|C| * (1 + Real.log x) + |C| * x ^ (s))) := by
        rw [Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x),
          Real.exp_log (by norm_num : (0:ℝ) < 3)]
        ring
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)

private theorem ne_top_and_toNat_le_of_le_one_add (a b : ℕ∞) (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_natCast]
  exact_mod_cast h'

theorem partARelax (w : ℝ) (hw : w < 11/20) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (M : AbF) (R : ℕ) (J Ct eps A1 : ℝ), 0 < J → 0 ≤ Ct → 0 < eps →
      ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ (X : ℝ) (q d : ℕ), PrimePair M.m q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∀ (L₀ : Type) [Field L₀] [NumberField L₀], TwoBase M q d L₀ → ABound 2 R L₀ →
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (w * eps / CK) Exc (t x) x →
            BaAt M eps e t q d x := by
  intro CK hCK hK M R J Ct eps A1 hJ hCt heps
  obtain ⟨n0, c0, hc0, hLD⟩ := layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two
    (by have := M.pos; omega)
  obtain ⟨C, hC0, hC⟩ := point2Relax w (1/4) CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2)
    hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := finalRelax ((w+1/4)*eps) Ct eps C heps (by nlinarith [mul_pos (sub_pos.mpr hw) heps])
  refine ⟨x0, fun e t hAdm X q d hPP hlogqd L₀ _ _ hTB hAB => ?_⟩
  obtain ⟨hmu, hfin, hcyc, hE⟩ := hTB
  have hSB : SecondBound 2 R L₀ := hAB.2
  obtain ⟨c, hζ, hZ⟩ := exc 2 R L₀ hAB
  have hc : c ≤ 16 * M.deg := by
    have h1 := rootdeg L₀ 2 c Nat.prime_two hζ
    have h2 : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu
  obtain ⟨Exc, hExc⟩ := hZ ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨he2, h2e, -, htx⟩ := hAdm x (by linarith)
  have hw : (1 : ℝ) ≤ x ^ (eps / 4) := Real.one_le_rpow hx1 (by positivity)
  have hP : 0 < q * d := Nat.mul_pos hPP.1.pos hPP.2.2.1.pos
  have hlogP : Real.log ((q * d : ℕ) : ℝ) ≤ x ^ (eps / 4) := by
    push_cast
    exact hlogqd.trans (logs.2.1 J eps X x hJ heps hX1 hXx)
  have hcyc' : Nonempty (L₀ →ₐ[ℚ] CyclotomicField (4 * M.m * (q * d)) ℚ) := by
    rw [← mul_assoc]; exact hcyc
  obtain ⟨hn0, hdisc⟩ := hLD (q * d) (x ^ (eps / 4)) hP hw hlogP L₀ L₂ hfin hcyc' hL₂
  obtain ⟨m, L₁, j1, j2, j3, hL₁, hme, hsha⟩ := hE (e x) he2 E hEc
  have hm : (m : ℝ) ≤ (2 * |A1| + 2) * (1 + Real.log x) := by
    have h3 := logs.2.2 (e x) A1 x hx1 h2e
    have h4 : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hme
    linarith
  have hpb : 0 ≤ pointCap C ((w+1/4)*eps) x := by
    show 0 ≤ C * (1 + Real.log x) + 2 * Real.exp (C * x ^ ((w+1/4)*eps))
    exact add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)
  show VVat 2 E (t x) (Real.exp (x ^ (4 * eps / 5)))
  refine vvat 2 (t x) E (x ^ Ct) (pointCap C ((w+1/4)*eps) x) _ hpb htx (hx0 x hx) ?_
  intro k hk1 hkt
  have hkx : (k : ℝ) ≤ x ^ Ct := le_trans (by exact_mod_cast hkt.le) htx
  have hk := hC L₀ hmu hSB c X Exc hc hExc L₂ hL₂ hn0 x hx1 hXx hxX (by convert hdisc using 1; ring_nf) k hk1 hkx (hG k hk1 hkt)
    m L₁ hL₁ hm
  obtain ⟨hne, hle⟩ := ne_top_and_toNat_le_of_le_one_add _ _ hk.1 (hsha k hk1)
  refine ⟨hne, ?_⟩
  have h5 : ((shaInv E 2 k).toNat : ℝ) ≤ 1 + ((shaInv L₁ 2 k).toNat : ℝ) := by
    exact_mod_cast hle
  linarith [hk.2]

private theorem exists_isPrimitiveRoot_of_hasMu_of_isAbField (A : AbF) (l : ℕ) [Fact l.Prime] (hA : A.HasMu l) (L : Type) [Field L]
    [NumberField L] (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨k, hk⟩ := hA.1.trans h1
  have hz : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ζ ^ k ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup j.fieldRange) := by
    rintro ⟨τ, hτ⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one
      (show (τ ζ) ^ N = 1 by rw [← map_pow, h2.pow_eq_one, map_one])
    have hker := (h3 τ a ha.symm).mp (fun x => hτ (j x) ⟨x, rfl⟩)
    have hmod := hA.2 a hker
    show τ (ζ ^ k) = ζ ^ k
    rw [map_pow, ← ha, ← pow_mul]
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        have hl1 : l ∣ 1 := Nat.modEq_zero_iff_dvd.mp hmod.symm
        exact absurd (Nat.le_of_dvd one_pos hl1) (not_le.mpr (Fact.out : l.Prime).one_lt)
      · exact h
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' ha1).mp hmod.symm
    have ha' : a = l * q + 1 := (Nat.sub_eq_iff_eq_add ha1).mp hq
    calc ζ ^ (a * k) = ζ ^ (k + N * q) := by
          congr 1
          rw [ha', hk]
          ring
      _ = ζ ^ k := by rw [pow_add, pow_mul, h2.pow_eq_one, one_pow, mul_one]
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := CyclotomicField N ℚ)
  rw [IsGalois.fixedField_fixingSubgroup] at key
  obtain ⟨y, hy⟩ := key
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).mp hz

theorem partBRelax (w : ℝ) (hw : w < 4/5) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ → ABound l R L₀ →
        ∀ J Ct eps A1 : ℝ, 0 < J → 0 ≤ Ct → 0 < eps → ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X : ℝ,
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (w * eps / CK) Exc (t x) x →
            ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField A L₀' →
              ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer l (jZero l R) L₀' L₁ →
                VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  intro CK hCK hK l R _ hl2 A hA L₀ _ _ hL₀ hAB J Ct eps A1 hJ hCt heps
  have hmu0 : HasMuQ l L₀ := by
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_hasMu_of_isAbField A l hA L₀ hL₀
    exact ⟨ζ, by rw [if_neg hl2]; exact hζ⟩
  obtain ⟨c, -, hc⟩ := exc l R L₀ hAB
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex l (jZero l R) Fact.out L₀ hmu0
  have hc0 : 0 ≤ Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((NumberField.discr L₂).natAbs : ℝ) :=
      Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₂))
    linarith
  obtain ⟨C, hC, hP⟩ := point2Relax w 0 CK hCK hK l R c (Module.finrank ℚ L₂)
    (Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))) J Ct eps (jZero l R : ℝ) hc0 hJ hCt heps
    (Nat.cast_nonneg _)
  obtain ⟨x1, hx1two, hx1⟩ := finalRelax ((w+0)*eps) Ct eps C heps (by nlinarith [mul_pos (sub_pos.mpr hw) heps])
  refine ⟨x1, fun e t hAdm X => ?_⟩
  obtain ⟨Exc, hExc⟩ := hc ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hgood L₀' _ _ hL₀' L₁ _ _ _ hL₁ => ?_⟩
  obtain ⟨f0⟩ := abiso A L₀ L₀' hL₀ hL₀'
  obtain ⟨f1⟩ := layeriso l (jZero l R) Fact.out L₀ L₀' L₂ L₁ ⟨f0⟩ hL₂ hL₁
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hadm := hAdm x (by linarith)
  have hQ : ∀ e' : ℕ, 1 ≤ e' → e' < t x → (e' : ℝ) ≤ x ^ Ct →
      shaInv L₂ l e' ≠ ⊤ ∧ ((shaInv L₂ l e').toNat : ℝ) + 1 ≤ pointCap C ((w+0)*eps) x := by
    intro e' he1 hactive he2
    refine hP L₀ hmu0 hAB.2 c X Exc le_rfl hExc L₂ hL₂ le_rfl x hx1' hXx hxX ?_ e' he1 he2 (hgood e' he1 hactive)
      (jZero l R) L₂ hL₂ ?_
    · simp
    · exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx1'])
  have hb : 0 ≤ pointCap C ((w+0)*eps) x := by
    unfold pointCap
    exact add_nonneg (mul_nonneg hC (by linarith [Real.log_nonneg hx1'])) (by positivity)
  refine vvat l (t x) L₁ (x ^ Ct) (pointCap C ((w+0)*eps) x) _ hb hadm.2.2.2 (hx1 x hx) ?_
  intro e' he1 he2
  rw [← shaInv_congr f1]
  have h := hQ e' he1 he2 (le_trans (by exact_mod_cast he2.le) hadm.2.2.2)
  exact ⟨h.1, by linarith [h.2]⟩

/-- Two frozen endpoint tests fill the interval when the earlier summation cutoff
exceeds the later allowed integer. No cardinality or connectedness assumption. -/
theorem fillActive {eta a x b : ℝ} {ta tx tb : ℕ} {E : Finset ℕ}
    (hax : a ^ eta ≤ x ^ eta) (hxb : tx ≤ tb)
    (hcross : b ^ eta < (ta : ℝ))
    (ha : ActiveSmall eta E ta a) (hb : ActiveSmall eta E tb b) :
    ActiveSmall eta E tx x := by
  intro k hk hkt hE
  by_cases hleft : k < ta
  · exact (ha k hk hleft hE).trans hax
  · have hkmin : (ta : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hleft)
    have hkmax := hb k hk (hkt.trans_le hxb) hE
    linarith

/-- A power-window corollary. The chosen source exponents satisfy these
inequalities throughout the analytic window as soon as its left endpoint is 2. -/
theorem fillPower {eta Ct lam a x b : ℝ} {E : Finset ℕ}
    (ha : 2 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ a ^ lam)
    (hCt : 2 ≤ Ct) (heta : 0 ≤ eta) (hscale : lam*eta ≤ 1)
    (hA : ActiveSmall eta E ⌊a^Ct⌋₊ a) (hB : ActiveSmall eta E ⌊b^Ct⌋₊ b) :
    ActiveSmall eta E ⌊x^Ct⌋₊ x := by
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hbx : b ^ eta ≤ a := by
    calc b ^ eta ≤ (a ^ lam) ^ eta := Real.rpow_le_rpow (by linarith) hb heta
      _ = a ^ (lam * eta) := (Real.rpow_mul ha0 _ _).symm
      _ ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hscale
      _ = a := Real.rpow_one _
  have h2 : a ^ (2 : ℕ) ≤ a ^ Ct := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le ha1 hCt
  have hc := Nat.lt_floor_add_one (a^Ct)
  apply fillActive (Real.rpow_le_rpow ha0 hax heta)
    (Nat.floor_mono (Real.rpow_le_rpow hx0 hxb (by linarith : 0 ≤ Ct))) _ hA hB
  nlinarith [sq_nonneg (a-2)]

/-- The original constants and one finite family of sets serve every ordinate
in the outer range satisfying the two active-weight predicates. -/
def Joint (K : BConst) (wA wB Ct : ℝ) : Prop :=
  ∀ (M : AbF) (B' : Finset ℕ) (L : ℕ → AbF), OddPrimesWithRootsOfUnity B' L →
    ∀ eps A1 : ℝ, 0 < eps → eps < 1/52 → ∃ X0 : ℝ, ∀ e t : ℝ → ℕ,
    admitted A1 Ct e t → ∀ X ≥ X0, ∀ q d : ℕ, PrimePair M.m q d →
      Real.log ((q : ℝ)*d) ≤ X ^ (eps/(4*K.J Ct eps M B' L)) →
      ∃ (EA : Finset ℕ) (EB : ℕ → Finset ℕ),
        EA.card ≤ K.R0 M ∧ (∀ l ∈ B', (EB l).card ≤ K.Rl l (L l)) ∧
        ∀ x : ℝ, X ^ (1/(K.J Ct eps M B' L)) ≤ x → x ≤ X →
          ActiveSmall (wA * eps / K.CK) EA (t x) x →
          (∀ l ∈ B', ActiveSmall (wB * eps / K.CK) (EB l) (t x) x) →
          BaAt M eps e t q d x ∧ BbAt K B' L eps t x

theorem joint (wA wB : ℝ) (ha : wA < 11/20) (hb : wB < 4/5) :
    (∃ CK : ℝ, LemmaK CK) → FixedIn → TwoIn → ∃ K : BConst,
      1 ≤ K.CK ∧ ∀ Ct : ℝ, 1 ≤ Ct → Joint K wA wB Ct := by
  rintro ⟨CK0, hK0⟩ hF hT
  classical
  have hCK1 : (1 : ℝ) ≤ max CK0 1 := le_max_right _ _
  have hCKpos : (0 : ℝ) < max CK0 1 := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaK (max CK0 1) := kmono CK0 _ (le_max_left _ _) hK0
  let P : ℕ → AbF → ℕ → Prop := fun l A R =>
    ∃ (_ : Fact l.Prime) (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField A L₀ ∧ ABound l R L₀
  let R0 : AbF → ℕ := fun M => Classical.choose (hT M)
  let Rl : ℕ → AbF → ℕ := fun l A => if h : ∃ R, P l A R then Classical.choose h else 0
  refine ⟨BConst.mk R0 Rl (max CK0 1) hCKpos, hCK1, fun Ct hCt => ?_⟩
  unfold Joint
  intro M B' L hAux eps A1 heps heps'
  unfold OddPrimesWithRootsOfUnity at hAux
  have hCt0 : 0 < Ct := lt_of_lt_of_le one_pos hCt
  set CK : ℝ := max CK0 1 with hCKdef
  set R : ℕ := R0 M + ∑ l ∈ B', Rl l (L l) with hRdef
  set J : ℝ := 2 ^ (R + 2) * (2 * CK * Ct / eps) ^ R with hJdef
  have hJpos : 0 < J := by
    have : 0 < 2 * CK * Ct / eps := by positivity
    positivity
  obtain ⟨x0A, hA⟩ := partARelax wA ha CK hCKpos hK M (R0 M) J Ct eps A1 hJpos hCt0.le heps
  have hB : ∀ l ∈ B', ∃ x0 : ℝ, ∀ e t, admitted A1 Ct e t → ∀ X : ℝ, ∃ Exc : Finset ℕ,
      Exc.card ≤ Rl l (L l) ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (wB * eps / CK) Exc (t x) x →
        ∀ (_ : Fact l.Prime) (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField (L l) L₀' →
          ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁],
            IsLayer l (Nat.log l (Rl l (L l)) + 3) L₀' L₁ → VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
    intro l hl
    obtain ⟨hp, hl2, hmu⟩ := hAux l hl
    haveI : Fact l.Prime := ⟨hp⟩
    by_cases hex : ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀), IsAbField (L l) L₀
    · obtain ⟨L₀, _, _, hab⟩ := hex
      have hP : ∃ R, P l (L l) R := by
        obtain ⟨R', hR'⟩ := hF l hl2 (L l) hmu L₀ hab
        exact ⟨R', ⟨_, L₀, _, _, hab, hR'⟩⟩
      have hRl : Rl l (L l) = Classical.choose hP := by
        show (if h : ∃ R, P l (L l) R then Classical.choose h else 0) = _
        rw [dif_pos hP]
      obtain ⟨_, L₀₀, _, _, hab0, hR0⟩ := Classical.choose_spec hP
      obtain ⟨x0, hx0⟩ := partBRelax wB hb CK hCKpos hK l (Classical.choose hP) hl2 (L l) hmu L₀₀ hab0 hR0
        J Ct eps A1 hJpos hCt0.le heps
      refine ⟨x0, fun e t hAdm X => ?_⟩
      obtain ⟨Exc, hcard, hx⟩ := hx0 e t hAdm X
      refine ⟨Exc, hRl ▸ hcard, fun x hxx hlo hhi hg _ L₀' _ _ hab' L₁ _ _ _ hlay => ?_⟩
      rw [hRl] at hlay
      exact hx x hxx hlo hhi hg L₀' hab' L₁ hlay
    · refine ⟨0, fun e t _ X => ⟨∅, by simp, ?_⟩⟩
      intro x _ _ _ _ _ L₀' _ _ hab' _ _ _ _ _
      exact absurd ⟨L₀', _, _, hab'⟩ hex
  choose! f hf using hB
  set x1 : ℝ := max 1 (max x0A (∑ l ∈ B', |f l|)) with hx1def
  have hfle : ∀ l ∈ B', f l ≤ x1 := fun l hl =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hl).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hx0A : x0A ≤ x1 := (le_max_left _ _).trans (le_max_right _ _)
  have hx1pos : 0 ≤ x1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 2 (x1 ^ J), fun e t hAdm X hX q d hqd hlog => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXJ : x1 ^ J ≤ X := (le_max_right _ _).trans hX
  have hlow : x1 ≤ X ^ (1 / J) := by
    calc x1 = (x1 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx1pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx1pos _) hXJ (by positivity)
  obtain ⟨L₀, _, _, hTB, hAB⟩ := Classical.choose_spec (hT M) q d hqd
  obtain ⟨ExcA, hcardA, hxA⟩ := hA e t hAdm X q d hqd hlog L₀ hTB hAB
  have hB2 := fun l hl => hf l hl e t hAdm X
  choose! g hg using hB2
  refine ⟨ExcA, g, hcardA, fun l hl => (hg l hl).1, ?_⟩
  intro x hXlo hXhi hAact hBact
  refine ⟨hxA x (hx0A.trans (hlow.trans hXlo)) hXlo hXhi hAact, ?_⟩
  unfold BbAt
  intro l hl _ L₀' _ _ hab L₁ _ _ _ hlay
  exact (hg l hl).2 x ((hfle l hl).trans (hlow.trans hXlo)) hXlo hXhi
    (hBact l hl) _ L₀' hab L₁ hlay

open IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal
  UpperTheory.V.Base UpperTheory.V.HV
theorem heightAt (hP : PointHV) (K : BConst) (Ct : ℝ) (hCt : 0 < Ct) (ψ : PChar) :
    ∃ C : ℝ, ∃ r₁ r₂ : ℕ, ∀ (eps A1 : ℝ) (e t : ℝ → ℕ), admitted A1 Ct e t →
      ∀ (X x : ℝ) (q d : ℕ), 2 ≤ x → x ≤ X → PrimePair ψ.N q d →
      2 * X^Ct + 1 < (q : ℝ) → 2 * X^Ct + 1 < (d : ℝ) →
      (∀ k ∈ [ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂], k < q ∧ k < d) →
      BbAt K (Bchi ψ) (Lchi ψ) eps t x → HVAt ψ C eps e t q d x := by
  obtain ⟨C, r₁, r₂, _, _, hmain⟩ := hP ψ (fun l => Nat.log l (K.Rl l (Lchi ψ l)) + 3)
  refine ⟨(C : ℝ), r₁, r₂, ?_⟩
  intro eps A1 e t hadm X x q d hx2 hxX hpair hq hd hlist hBb
  obtain ⟨he2, -, ht2, htx⟩ := hadm x hx2
  have htX : (t x : ℝ) ≤ X ^ Ct := le_trans htx (Real.rpow_le_rpow (by linarith) hxX hCt.le)
  intro E _ _ _ hE
  have hq' : 2 * t x + 1 < q := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < q by linarith)
  have hd' : 2 * t x + 1 < d := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < d by linarith)
  have hbig : Host.Big ⟨ψ, e x, q, d, he2, hpair⟩ (t x) := by
    refine ⟨hq', hd', ?_⟩
    intro y hy
    apply hlist y
    simp only [Host.q, Host.o, List.mem_cons, List.not_mem_nil] at hy ⊢
    tauto
  have key := hmain ⟨ψ, e x, q, d, he2, hpair⟩ rfl
    (hlist r₁ (by simp)).1 (hlist r₁ (by simp)).2 (hlist r₂ (by simp)).1 (hlist r₂ (by simp)).2
    (t x) ht2 hbig (Real.exp (x ^ (4 * eps / 5))) (Real.exp_pos _).le
    (fun l hl _ => hBb l hl) E hE
  rw [hostCond ⟨ψ, e x, q, d, he2, hpair⟩ E hE]
  simpa [Real.rpow_natCast] using key


theorem fieldAt (ψ : PChar) (Ct C eps : ℝ) (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (heps52 : eps < 1/52) (hc : ThmBc Ct)
    (e : ℝ → ℕ) (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (V : ℝ) (q d : ℕ), WinPair eps V q d → PrimePair ψ.N q d →
      Real.log ((q : ℝ) * d) ≤ x ^ (eps/4) →
      BaAt (AbF.ofChar ψ) eps e (fun u => ⌊u^Ct⌋₊) q d x →
      HVAt ψ C eps e (fun u => ⌊u^Ct⌋₊) q d x →
      VAt ψ eps Ct q d (e x) x := by
  set t : ℝ → ℕ := fun u => ⌊u ^ Ct⌋₊
  have hadm : admitted 4 Ct e t := admissible_of_pageN heps heps52 hCt he
  obtain ⟨Cb, hCb⟩ := hc
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le Cb (AbF.ofChar ψ).deg
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C heps
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N heps heps52
  let L := max (max xT xN) (2 : ℝ)
  have hxTL : xT ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hxNL : xN ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨L, ?_⟩
  intro x hLx V q d hw hpp hqd hBa hHV
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hLx
  have hx1 : 1 ≤ x := by linarith
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  have hm := hCb (AbF.ofChar ψ) 4 e t hadm x hx2 q d hpp E hE'
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (Module.finrank ℚ E) (condF E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hm' := VVminusLe.mono hm hmb
  have hv := vvle_of_parts h2 hm' hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  exact VVle.mono hv le_rfl htot

/-- One collection of sets and one prime pair can be evaluated at arbitrarily
many certified ordinates of the outer range. The inputs remain explicit. -/
theorem fieldTransport (wA wB : ℝ) (K : BConst) (Ct eps : ℝ) (psi : PChar)
    (hCt : 1 ≤ Ct) (heps : 0 < eps) (heps52 : eps < 1/52)
    (hj : Joint K wA wB Ct) (hp : PointHV) (hc : ThmBc Ct)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    ∃ r₁ r₂ : ℕ, ∃ L X0 : ℝ, ∀ X ≥ X0, ∀ (V : ℝ) (q d : ℕ),
      WinPair eps V q d → PrimePair psi.N q d →
      2*X^Ct+1 < (q:ℝ) → 2*X^Ct+1 < (d:ℝ) →
      (∀ k ∈ [psi.N, ordC psi, pK psi, hStar psi, pOne psi, r₁, r₂], k < q ∧ k < d) →
      Real.log ((q:ℝ)*d) ≤ X ^ (eps/(4*Jchi K Ct eps psi)) →
      ∃ (EA : Finset ℕ) (EB : ℕ → Finset ℕ),
        EA.card ≤ K.R0 (AbF.ofChar psi) ∧ (∀ l ∈ Bchi psi, (EB l).card ≤ K.Rl l (Lchi psi l)) ∧
        ∀ x ≥ L, X ^ (1/Jchi K Ct eps psi) ≤ x → x ≤ X →
          ActiveSmall (wA*eps/K.CK) EA ⌊x^Ct⌋₊ x →
          (∀ l ∈ Bchi psi, ActiveSmall (wB*eps/K.CK) (EB l) ⌊x^Ct⌋₊ x) →
          VAt psi eps Ct q d (e x) x := by
  let t : ℝ → ℕ := fun x => ⌊x^Ct⌋₊
  have ht := admissible_of_pageN heps heps52 hCt hpage
  have hct0 : 0 < Ct := by linarith
  have hJ : 0 < Jchi K Ct eps psi := BConst.J_pos K hct0 heps _ _ _
  obtain ⟨X0,hX0⟩ := hj (AbF.ofChar psi) (Bchi psi) (Lchi psi) (primeSetBoundData_of_primitiveChar psi) eps 4 heps heps52
  obtain ⟨C, r₁, r₂, hheight⟩ := heightAt hp K Ct hct0 psi
  obtain ⟨L,hL⟩ := fieldAt psi Ct C eps hCt heps heps52 hc e hpage
  refine ⟨r₁,r₂,max 2 L,X0,?_⟩
  intro X hX V q d hw hpair hq hd hlist hlog
  obtain ⟨EA,EB,hEA,hEB,hh⟩ := hX0 e t ht X hX q d hpair hlog
  refine ⟨EA,EB,hEA,hEB,?_⟩
  intro x hLx hxlo hxhi hactA hactB
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hLx
  have hloc := hh x hxlo hxhi hactA hactB
  have hv := hheight eps 4 e t ht X x q d hx2 hxhi hpair hq hd hlist hloc.2
  have hlogx := hlog.trans (logs.2.1 _ eps X x hJ heps (by linarith) hxlo)
  exact hL x ((le_max_right _ _).trans hLx) V q d hw hpair hlogx hloc.1 hv
/-- Supply two active endpoint certificates to the field-valued local transport.
The same parameters appear throughout the interval. -/
theorem fieldFill (psi : PChar) (e : ℝ → ℕ) (eps Ct a x b lam ea eb : ℝ)
    (q d : ℕ) (EA : Finset ℕ) (EB : ℕ → Finset ℕ)
    (hCt : 2 ≤ Ct) (ha : 2 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ a^lam)
    (hea : 0 ≤ ea) (heb : 0 ≤ eb) (hsa : lam*ea ≤ 1) (hsb : lam*eb ≤ 1)
    (hloc : ∀ y, a ≤ y → y ≤ b → ActiveSmall ea EA ⌊y^Ct⌋₊ y →
      (∀ l ∈ Bchi psi, ActiveSmall eb (EB l) ⌊y^Ct⌋₊ y) → VAt psi eps Ct q d (e y) y)
    (hleftA : ActiveSmall ea EA ⌊a^Ct⌋₊ a)
    (hleftB : ∀ l ∈ Bchi psi, ActiveSmall eb (EB l) ⌊a^Ct⌋₊ a)
    (hrightA : ActiveSmall ea EA ⌊b^Ct⌋₊ b)
    (hrightB : ∀ l ∈ Bchi psi, ActiveSmall eb (EB l) ⌊b^Ct⌋₊ b) :
    VAt psi eps Ct q d (e x) x :=
  hloc x hax hxb (fillPower ha hax hxb hb hCt hea hsa hleftA hrightA)
    (fun l hl => fillPower ha hax hxb hb hCt heb hsb (hleftB l hl) (hrightB l hl))
/-- At the source scale a genuine WinPair supplies every common size condition,
including the exceptional auxiliary primes of the pointwise height theorem. -/
theorem windowPairTransport (wA wB : ℝ) (K : BConst) (Ct eps : ℝ) (psi : PChar)
    (hCt : 1 ≤ Ct) (heps : 0 < eps) (heps52 : eps < 1/52)
    (hj : Joint K wA wB Ct) (hp : PointHV) (hc : ThmBc Ct)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1/Jchi K Ct eps psi)) q d →
      ∃ (EA : Finset ℕ) (EB : ℕ → Finset ℕ),
        EA.card ≤ K.R0 (AbF.ofChar psi) ∧ (∀ l ∈ Bchi psi, (EB l).card ≤ K.Rl l (Lchi psi l)) ∧
        ∀ x, X ^ (1/Jchi K Ct eps psi) ≤ x → x ≤ X →
          ActiveSmall (wA*eps/K.CK) EA ⌊x^Ct⌋₊ x →
          (∀ l ∈ Bchi psi, ActiveSmall (wB*eps/K.CK) (EB l) ⌊x^Ct⌋₊ x) →
          VAt psi eps Ct q d (e x) x := by
  set J := Jchi K Ct eps psi
  have hJ : 0 < J := BConst.J_pos K (by linarith) heps _ _ _
  obtain ⟨r₁,r₂,L,X0,hmain⟩ := fieldTransport wA wB K Ct eps psi hCt heps heps52 hj hp hc e hpage
  let indices := [psi.N, ordC psi, pK psi, hStar psi, pOne psi, r₁, r₂]
  obtain ⟨XB,hXB⟩ := eventually_winPair_gt_power eps J Ct (indices.sum : ℝ) heps hJ
  obtain ⟨Y0,hY0⟩ := log_mul_le_rpow_of_winPair eps heps
  set T := max 2 (max L Y0)
  have hT : 2 ≤ T := le_max_left _ _
  have hTL : L ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTY : Y0 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max (max X0 XB) (T ^ J), ?_⟩
  intro X hX q d hw
  have hX0 : X0 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXB' : XB ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hTX : T^J ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hTX
  have hlow : T ≤ X ^ (1/J) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ T) J) hTX (by positivity : 0 ≤ 1/J)
    rwa [← Real.rpow_mul (by linarith : 0 ≤ T), mul_one_div_cancel hJ.ne', Real.rpow_one] at h
  obtain ⟨hq,hd,hPq,hPd⟩ := hXB X hXB' q d hw
  have hlist : ∀ k ∈ indices, k < q ∧ k < d := by
    intro k hk
    have hsum : k ≤ indices.sum := List.le_sum_of_mem hk
    have hcast : (k:ℝ) ≤ (indices.sum:ℝ) := by exact_mod_cast hsum
    exact ⟨by exact_mod_cast hcast.trans_lt hPq, by exact_mod_cast hcast.trans_lt hPd⟩
  have hcop : ∀ r : ℕ, r.Prime → psi.N < r → r.Coprime psi.N := by
    intro r hr hlt
    have hN : 0 < psi.N := (AbF.ofChar psi).pos
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => (not_le_of_gt hlt) (Nat.le_of_dvd hN hdvd))
  have hN := hlist psi.N (by simp [indices])
  have hpp : PrimePair psi.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul (hcop q hw.q_prime hN.1) (hcop d hw.d_prime hN.2)⟩
  have hlog := hY0 _ (hTY.trans hlow) q d hw
  have hpow : (X^(1/J))^(eps/4) = X^(eps/(4*J)) := by
    rw [← Real.rpow_mul hXpos.le]
    congr 1
    field_simp
  rw [hpow] at hlog
  obtain ⟨EA,EB,hA,hB,hall⟩ := hmain X hX0 _ q d hw hpp hq hd hlist hlog
  exact ⟨EA,EB,hA,hB,fun x hx hx' => hall x ((hTL.trans hlow).trans hx) hx hx'⟩
/-- Fix the joint prime witness before exposing any endpoint test. The retained
PairGood includes original twist estimates and boxes on the whole outer interval. -/
theorem commonPairGood (wA wB : ℝ) (K : BConst) (hK1 : 1 ≤ K.CK)
    (Ct eps : ℝ) (psi : PChar) (hCt : 1 ≤ Ct) (heps : 0 < eps) (heps52 : eps < 1/52)
    (hj : Joint K wA wB Ct) (hp : PointHV) (hc : ThmBc Ct) (hpair : PairEx)
    (e : ℝ → ℕ) (hpage : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    let J := Jchi K Ct eps psi
    ∃ X0 : ℝ, ∀ X ≥ X0, ∃ (q d : ℕ) (EA : Finset ℕ) (EB : ℕ → Finset ℕ),
      PairGood psi.N eps (X ^ (1/J)) X q d ∧
        EA.card ≤ K.R0 (AbF.ofChar psi) ∧ (∀ l ∈ Bchi psi, (EB l).card ≤ K.Rl l (Lchi psi l)) ∧
        ∀ x, X ^ (1/J) ≤ x → x ≤ X →
          ActiveSmall (wA*eps/K.CK) EA ⌊x^Ct⌋₊ x →
          (∀ l ∈ Bchi psi, ActiveSmall (wB*eps/K.CK) (EB l) ⌊x^Ct⌋₊ x) →
          VAt psi eps Ct q d (e x) x := by
  let J := Jchi K Ct eps psi
  have hJ1 : 1 ≤ J := by
    have hratio : 1 ≤ 2*K.CK*Ct/eps := (le_div_iff₀ heps).2 (by nlinarith [mul_nonneg (sub_nonneg.mpr hK1) (sub_nonneg.mpr hCt)])
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (one_le_pow₀ hratio)
  have hJ : 0 < J := zero_lt_one.trans_le hJ1
  obtain ⟨X0,hX0⟩ := windowPairTransport wA wB K Ct eps psi hCt heps heps52 hj hp hc e hpage
  obtain ⟨Y0,hY0⟩ := hpair psi.N (AbF.ofChar psi).pos eps J heps heps52 hJ1
  set T := max 2 Y0
  have hT : 0 < T := by have := le_max_left (2:ℝ) Y0; linarith
  refine ⟨max X0 (T^J), ?_⟩
  intro X hX
  have hT' : T^J ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := (Real.rpow_pos_of_pos hT J).trans_le hT'
  have hlow : T ≤ X^(1/J) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hT.le J) hT' (by positivity : 0 ≤ 1/J)
    rwa [← Real.rpow_mul hT.le, mul_one_div_cancel hJ.ne', Real.rpow_one] at h
  obtain ⟨q,d,hgood⟩ := hY0 _ ((le_max_right _ _).trans hlow)
  have hxid : (X^(1/J))^J = X := by rw [one_div,Real.rpow_inv_rpow hXpos.le hJ.ne']
  rw [hxid] at hgood
  obtain ⟨EA,EB,hA,hB,hall⟩ := hX0 X ((le_max_left _ _).trans hX) q d hgood.pair
  exact ⟨q,d,EA,EB,hgood,hA,hB,hall⟩

end EndpointWeights
end
#print axioms EndpointWeights.kexpRelax
#print axioms EndpointWeights.pointRelax
#print axioms EndpointWeights.point2Relax
#print axioms EndpointWeights.finalRelax
#print axioms EndpointWeights.partARelax
#print axioms EndpointWeights.partBRelax
#print axioms EndpointWeights.fillActive
#print axioms EndpointWeights.joint
#print axioms EndpointWeights.heightAt
#print axioms EndpointWeights.fieldAt

#print axioms EndpointWeights.fillPower
#print axioms EndpointWeights.fieldTransport

#print axioms EndpointWeights.fieldFill

#print axioms EndpointWeights.windowPairTransport

#print axioms EndpointWeights.commonPairGood
