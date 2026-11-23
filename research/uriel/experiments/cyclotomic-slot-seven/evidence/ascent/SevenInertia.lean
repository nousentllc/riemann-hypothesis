import SevenClassStep
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

noncomputable section

open NumberField IsDedekindDomain IntermediateField Ideal GroundTheory.Global
open scoped Pointwise

namespace Seven.Inertia

section
variable {F E U : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  [Field U] [NumberField U] [Algebra F E] [Algebra F U] [Algebra E U] [IsScalarTower F E U]
  [IsGalois F U]

/-- An everywhere-unramified upstairs step does not alter the order of inertia. -/
theorem relative_inertia_card (hu : IsUnramifiedEverywhere E U)
    (v : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 U)) [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    Nat.card (Q.inertia Gal(U/F)) = (Q.under (𝓞 E)).ramificationIdx (𝓞 F) := by
  have hb : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q.under (𝓞 E), inferInstance, Ideal.under_ne_bot _ hb⟩
  have hw : Q.LiesOver w.asIdeal := by
    change Q.LiesOver (Q.under (𝓞 E))
    infer_instance
  have := v.isMaximal
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  calc
    Nat.card (Q.inertia Gal(U/F)) = v.asIdeal.ramificationIdxIn (𝓞 U) :=
      Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(U/F)) v.asIdeal Q
    _ = Q.ramificationIdx (𝓞 F) := ramificationIdxIn_eq_ramificationIdx _ Q Gal(U/F)
    _ = _ := by rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal Q,
                       (hu.1 w).ramificationIdx_eq_one hw, mul_one]

end

section
variable {F U : Type} [Field F] [NumberField F] [Field U] [NumberField U] [Algebra F U]
  [IsGalois F U]

theorem inertia_conjugates_le_normal (H : Subgroup Gal(U/F)) [H.Normal]
    (p : Ideal (𝓞 F)) (Q Q' : Ideal (𝓞 U)) [Q.IsPrime] [Q'.IsPrime]
    [Q.LiesOver p] [Q'.LiesOver p] (h : Q.inertia Gal(U/F) ≤ H) :
    Q'.inertia Gal(U/F) ≤ H := by
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p Q Q' Gal(U/F)
  intro σ hσ
  rw [← hg, mem_inertia_smul_iff] at hσ
  have hc := (inferInstance : H.Normal).conj_mem (g⁻¹ * σ * g) (h hσ) g
  simpa [mul_assoc] using hc

/-- Restrict inertia onto a normal fixed field. Containment in its fixing subgroup
forces every finite inertia group in that fixed field to be trivial. -/
theorem fixed_unramified [IsTotallyComplex F] (H : Subgroup Gal(U/F)) [H.Normal]
    (h : ∀ (v : HeightOneSpectrum (𝓞 F)) (Q : Ideal (𝓞 U)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Q.inertia Gal(U/F) ≤ H) : IsUnramifiedEverywhere F (fixedField H) := by
  let M := fixedField H
  change IsUnramifiedEverywhere F M
  constructor
  · intro v
    apply Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mpr
    intro P hP hp
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := P.nonempty_primesOver (S := 𝓞 U)
    have hv := Ideal.LiesOver.trans Q P v.asIdeal
    have hker : Q.inertia Gal(U/F) ≤ (AlgEquiv.restrictNormalHom M).ker := by
      rw [M.restrictNormalHom_ker]
      change Q.inertia Gal(U/F) ≤ (fixedField H).fixingSubgroup
      rw [IntermediateField.fixingSubgroup_fixedField]
      exact h v Q
    have hBot : (Q.inertia Gal(U/F)).map (AlgEquiv.restrictNormalHom M) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact hker
    rw [map_inertia_restrictNormalHom, ← Ideal.over_def Q P] at hBot
    have := v.isMaximal
    have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    rw [← ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(M/F),
      ← card_inertia_eq_ramificationIdxIn (G := Gal(M/F)) v.asIdeal P, Subgroup.card_eq_one]
    exact hBot
  · intro v w hw
    rw [InfinitePlace.isUnramified_iff, hw]
    exact Or.inr (IsTotallyComplex.isComplex v)

end
/-- One possible finite ramification place suffices; the relative inertia size
is a downstairs quantity since the cover of E is everywhere unramified. -/
theorem descend {p : ℕ} [Fact p.Prime] (F E U : Type)
    [Field F] [NumberField F] [Field E] [NumberField E] [Field U] [NumberField U]
    [Algebra F E] [Algebra E U] [Algebra F U] [IsScalarTower F E U]
    [IsGalois F E] [IsGalois F U] [IsTotallyComplex F]
    (v : HeightOneSpectrum (𝓞 F))
    (ram : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal],
      P.ramificationIdx (𝓞 F) ≤ p)
    (away : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → Algebra.IsUnramifiedIn (𝓞 E) w.asIdeal)
    (hu : IsUnramifiedEverywhere E U) (hp : IsPGroup p Gal(U/F))
    (hbig : p < Nat.card Gal(U/F)) :
    ∃ M : IntermediateField F U, IsAbelianGalois F M ∧ Module.finrank F M = p ∧
      IsUnramifiedEverywhere F M := by
  classical
  let _ := v.isMaximal
  obtain ⟨⟨Q, hQ, hQv⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 U)
  have hP : (Q.under (𝓞 E)).LiesOver v.asIdeal := Ideal.LiesOver.tower_bot Q _ v.asIdeal
  have hi : Nat.card (Q.inertia Gal(U/F)) ≤ p :=
    (relative_inertia_card hu v Q).le.trans (ram _)
  have hproper : Q.inertia Gal(U/F) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top] at hi
    omega
  obtain ⟨H, hH, hn, hidx⟩ := Seven.ClassStep.prime_quotient_of_proper hp _ hproper
  let M := fixedField H
  have hd : Module.finrank F M = p := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField, hidx]
  have hc : Nat.card Gal(M/F) = p := (IsGaloisGroup.card_eq_finrank _ F M).trans hd
  have hcyc : IsCyclic Gal(M/F) := isCyclic_of_prime_card hc
  have hab : IsAbelianGalois F M := {}
  refine ⟨M, hab, hd, fixed_unramified H ?_⟩
  intro w Q' hQ' hQw
  by_cases same : w = v
  · subst w
    exact inertia_conjugates_le_normal H v.asIdeal Q Q' hH
  · have hPw : (Q'.under (𝓞 E)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q' _ w.asIdeal
    have h1 : Nat.card (Q'.inertia Gal(U/F)) = 1 :=
      (relative_inertia_card hu w Q').trans ((away w same).ramificationIdx_eq_one hPw)
    rw [Subgroup.card_eq_one.mp h1]
    exact bot_le
end Seven.Inertia
end

#print axioms Seven.Inertia.relative_inertia_card
#print axioms Seven.Inertia.inertia_conjugates_le_normal
#print axioms Seven.Inertia.fixed_unramified
#print axioms Seven.Inertia.descend
