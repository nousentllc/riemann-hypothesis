import NextLayer
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus

noncomputable section

open NumberField IsDedekindDomain IntermediateField Ideal GroundTheory.Global
open scoped Pointwise

namespace SlotThree.InertiaDescent

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
open SlotThree.NextLayer

/-- Descend an unramified extension of a cubic layer, provided the upstairs Galois
group has order greater than three and its proper subgroups lie in a normal subgroup
of index three. The latter is the finite 3-group lemma. -/
theorem descend (k : ℕ) (U : Type) [Field U] [NumberField U]
    [Algebra (Lower k) U] [Algebra (Upper k) U] [IsScalarTower (Lower k) (Upper k) U]
    [IsGalois (Lower k) U] (hu : IsUnramifiedEverywhere (Upper k) U)
    (hbig : 3 < Nat.card Gal(U/Lower k))
    (select : ∀ I : Subgroup Gal(U/Lower k), I ≠ ⊤ →
      ∃ H : Subgroup Gal(U/Lower k), I ≤ H ∧ H.Normal ∧ H.index = 3) :
    ∃ M : IntermediateField (Lower k) U,
      IsAbelianGalois (Lower k) M ∧ Module.finrank (Lower k) M = 3 ∧
      IsUnramifiedEverywhere (Lower k) M := by
  classical
  let _ := totally_complex k
  let _ := step_galois k
  obtain ⟨p, hsing⟩ := Set.ncard_eq_one.mp (unique_over_three k)
  have hpMem : p ∈ (overPrime 3).primesOver (𝓞 (Lower k)) := hsing ▸ Set.mem_singleton _
  obtain ⟨hp, hp3⟩ := hpMem
  let v : HeightOneSpectrum (𝓞 (Lower k)) :=
    ⟨p, hp, Ideal.ne_bot_of_liesOver_of_ne_bot (show overPrime 3 ≠ ⊥ by norm_num [overPrime]) p⟩
  let _ := v.isMaximal
  obtain ⟨⟨Q, hQ, hQv⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 U)
  have hP : (Q.under (𝓞 (Upper k))).LiesOver v.asIdeal := Ideal.LiesOver.tower_bot Q _ v.asIdeal
  have h3 : Nat.card (Q.inertia Gal(U/Lower k)) = 3 := by
    rw [relative_inertia_card hu v Q, ← ramificationIdxIn_eq_ramificationIdx v.asIdeal
      (Q.under (𝓞 (Upper k))) Gal(Upper k / Lower k)]
    exact (ramification_three k p).2.1
  have hproper : Q.inertia Gal(U/Lower k) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top] at h3
    omega
  obtain ⟨H, hH, hn, hi⟩ := select _ hproper
  let M := fixedField H
  have hd : Module.finrank (Lower k) M = 3 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField, hi]
  have hc : Nat.card Gal(M/Lower k) = 3 :=
    (IsGaloisGroup.card_eq_finrank _ (Lower k) M).trans hd
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcyc : IsCyclic Gal(M/Lower k) := isCyclic_of_prime_card hc
  have hab : IsAbelianGalois (Lower k) M := {}
  refine ⟨M, hab, hd, fixed_unramified H ?_⟩
  intro w Q' hQ' hQw
  by_cases h3w : w.asIdeal.LiesOver (overPrime 3)
  · have hmem : w.asIdeal ∈ (overPrime 3).primesOver (𝓞 (Lower k)) := ⟨w.isPrime, h3w⟩
    have heq : w.asIdeal = v.asIdeal := by simpa only [hsing, Set.mem_singleton_iff] using hmem
    have hQp : Q'.LiesOver v.asIdeal := heq ▸ hQw
    exact inertia_conjugates_le_normal H v.asIdeal Q Q' hH
  · have hP' : (Q'.under (𝓞 (Upper k))).LiesOver w.asIdeal :=
      Ideal.LiesOver.tower_bot Q' _ w.asIdeal
    have hw := (unramified_iff k w.asIdeal w.ne_bot).mpr h3w
    have h1 : Nat.card (Q'.inertia Gal(U/Lower k)) = 1 :=
      (relative_inertia_card hu w Q').trans (hw.ramificationIdx_eq_one hP')
    rw [Subgroup.card_eq_one.mp h1]
    exact bot_le

#print axioms relative_inertia_card
#print axioms inertia_conjugates_le_normal
#print axioms fixed_unramified
#print axioms descend

end SlotThree.InertiaDescent
end
