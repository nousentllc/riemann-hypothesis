import FieldEndpoints
import CoherentFields

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win EndpointWeights CoherentFields
noncomputable section
namespace SynchronizedSlots
private theorem ne_top_and_toNat_le_of_le_one_add (a b : ℕ∞) (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_natCast]
  exact_mod_cast h'

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

theorem coherentPartA (w : ℝ) (hw : w < 11/20) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (M : AbF) (R : ℕ) (J Ct eps A1 : ℝ), 0 < J → 0 ≤ Ct → 0 < eps →
      ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ (q d : ℕ), PrimePair M.m q d →
        ∀ (L₀ : Type) [Field L₀] [NumberField L₀], TwoBase M q d L₀ → ABound 2 R L₀ →
          ∃ E : ℕ → Finset ℕ, OnOldRange E ∧ (∀ Z, (E Z).card ≤ R) ∧
          ∀ X : ℝ, Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
          ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (w * eps / CK) (E ⌊X ^ Ct⌋₊) (t x) x →
            BaAt M eps e t q d x := by
  intro CK hCK hK M R J Ct eps A1 hJ hCt heps
  obtain ⟨n0, c0, hc0, hLD⟩ := layerdisc 2 (jZero 2 R) (8 * M.deg) (4 * M.m) Nat.prime_two
    (by have := M.pos; omega)
  obtain ⟨C, hC0, hC⟩ := point2Relax w (1/4) CK hCK hK 2 R (16 * M.deg) n0 c0 J Ct eps (2 * |A1| + 2)
    hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := finalRelax ((w+1/4)*eps) Ct eps C heps (by nlinarith [mul_pos (sub_pos.mpr hw) heps])
  refine ⟨x0, fun e t hAdm q d hPP L₀ _ _ hTB hAB => ?_⟩
  obtain ⟨hmu, hfin, hcyc, hE⟩ := hTB
  have hSB : SecondBound 2 R L₀ := hAB.2
  obtain ⟨c, table, hζ, hZ, hcTable⟩ := coherentFirst hAB
  have hc : c ≤ 16 * M.deg := by
    have h1 := rootdeg L₀ 2 c Nat.prime_two hζ
    have h2 : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex 2 (jZero 2 R) Nat.prime_two L₀ hmu
  refine ⟨table, hcTable, fun Z => (hZ Z).1, fun X hlogqd x hx hXx hxX hG E _ _ hEc => ?_⟩
  let Exc := table ⌊X ^ Ct⌋₊
  have hExc : FirstBound 2 R c L₀ ⌊X ^ Ct⌋₊ Exc := hZ _
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

theorem coherentPartB (w : ℝ) (hw : w < 4/5) :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ → ABound l R L₀ →
        ∀ J Ct eps A1 : ℝ, 0 < J → 0 ≤ Ct → 0 < eps → ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t →
          ∃ E : ℕ → Finset ℕ, OnOldRange E ∧ (∀ Z, (E Z).card ≤ R) ∧ ∀ X : ℝ,
          ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → ActiveSmall (w * eps / CK) (E ⌊X ^ Ct⌋₊) (t x) x →
            ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField A L₀' →
              ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer l (jZero l R) L₀' L₁ →
                VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  intro CK hCK hK l R _ hl2 A hA L₀ _ _ hL₀ hAB J Ct eps A1 hJ hCt heps
  have hmu0 : HasMuQ l L₀ := by
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_hasMu_of_isAbField A l hA L₀ hL₀
    exact ⟨ζ, by rw [if_neg hl2]; exact hζ⟩
  obtain ⟨c,table,_,hc,hctable⟩ := coherentFirst hAB
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
  refine ⟨x1, fun e t hAdm => ?_⟩
  refine ⟨table,hctable,fun Z => (hc Z).1, fun X x hx hXx hxX hgood L₀' _ _ hL₀' L₁ _ _ _ hL₁ => ?_⟩
  let Exc := table ⌊X ^ Ct⌋₊
  have hExc : FirstBound l R c L₀ ⌊X ^ Ct⌋₊ Exc := hc _
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


/-- Transfer the earlier active test through the late table and a strict crossover. -/
theorem fillFromTwoCutoffs {E : ℕ → Finset ℕ} (h : OnOldRange E)
    {u v ta tx tb : ℕ} {a x b eta : ℝ} (huv : u ≤ v) (hcut : ta ≤ u + 1)
    (ha : ActiveSmall eta (E u) ta a) (hb : ActiveSmall eta (E v) tb b)
    (hxt : tx ≤ tb) (ha0 : 0 ≤ a) (hax : a ≤ x) (he : 0 ≤ eta) (cross : b^eta < (ta:ℝ)) :
    ActiveSmall eta (E v) tx x := by
  exact mixedFill h huv hcut ha hb hxt (Real.rpow_le_rpow ha0 hax he) cross

end SynchronizedSlots
end
#print axioms SynchronizedSlots.coherentPartA
#print axioms SynchronizedSlots.coherentPartB
#print axioms SynchronizedSlots.fillFromTwoCutoffs
