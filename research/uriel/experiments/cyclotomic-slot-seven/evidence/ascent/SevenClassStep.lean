import SevenCover
import HilbertNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
open NumberField GroundTheory.Global
namespace Seven.ClassStep
noncomputable section
/-- A subgroup of a finite p-group that normally generates the group already equals it. -/
theorem inertia_eq_top_of_normalClosure {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (I : Subgroup G) (h : Subgroup.normalClosure (I : Set G) = ⊤) : I = ⊤ := by
  let _ := hG.isNilpotent
  rcases eq_top_or_exists_le_coatom I with hI | ⟨M, hm, hIM⟩
  · exact hI
  · have : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent (G := G)) hm
    exact (hm.1 ((top_le_iff.mp (h ▸ Subgroup.normalClosure_le_normal (N := M) hIM)))).elim

/-- An inertia subgroup strictly below a finite prime-power group fits inside a normal subgroup of
prime index. Its fixed field is the possible cyclic prime-degree obstruction downstairs. -/
theorem prime_quotient_of_proper {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hp : IsPGroup p G)
    (I : Subgroup G) (hI : I ≠ ⊤) :
    ∃ M : Subgroup G, I ≤ M ∧ M.Normal ∧ M.index = p := by
  obtain ⟨M, hm, hIM⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  let _ := hp.isNilpotent
  have hn := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := G)) hm
  refine ⟨M, hIM, hn, ?_⟩
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  obtain ⟨b, hb⟩ := (hp.to_subgroup M).exists_card_eq
  have hlt : b < a := by
    apply (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).mp
    rw [← ha, ← hb]
    exact lt_of_le_of_ne M.card_le_card_group (fun h => hm.1 (M.eq_top_of_card_eq h))
  have hd : p ^ (b + 1) ∣ Nat.card G := ha ▸ pow_dvd_pow _ hlt
  obtain ⟨N, hN, hMN⟩ := Sylow.exists_subgroup_card_pow_succ hd hb
  have hne : M ≠ N := by
    rintro rfl
    have hz : p ^ b < p ^ (b+1) := pow_lt_pow_right₀ (Fact.out : Nat.Prime p).one_lt (Nat.lt_succ_self _)
    omega
  have htop := hm.2 N (lt_of_le_of_ne hMN hne)
  rw [htop, Subgroup.card_top, pow_succ, ← hb] at hN
  have he := M.card_mul_index
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (he.trans hN)

/-- Multiply the two genuine extension degrees before applying the p-group criterion. -/
theorem cover_group {p : ℕ} [Fact p.Prime] (F E U : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field U] [NumberField U] [Algebra F E] [Algebra E U] [Algebra F U] [IsScalarTower F E U]
    [IsGalois F U] [IsGalois E U] (hdeg : Module.finrank F E = p)
    (hp : IsPGroup p Gal(U/E)) (hbig : 1 < Module.finrank E U) :
    IsPGroup p Gal(U/F) ∧ p < Nat.card Gal(U/F) := by
  have hcard : Nat.card Gal(U/F) = p * Module.finrank E U := by
    rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank F E U, hdeg]
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  rw [IsGalois.card_aut_eq_finrank] at hm
  refine ⟨IsPGroup.of_card (n := m+1) ?_, ?_⟩
  · rw [hcard, hm, pow_succ']
  · rw [hcard]
    simpa using (Nat.mul_lt_mul_of_pos_left hbig (Fact.out : Nat.Prime p).pos)

open GroundTheory.Global IsDedekindDomain IdeleGroup SemiLocal

private theorem rec_index (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E] : (reciprocityMap K E).ker.index = Module.finrank K E := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr reciprocityMap_surjective,
    Subgroup.card_top, IsGalois.card_aut_eq_finrank]

/-- The Artin maps for an abstract everywhere-unramified abelian extension and the Hilbert
class field factor through nested kernels. Their indices give this divisibility of degrees. -/
theorem unramified_degree_dvd (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E] (hu : IsUnramifiedEverywhere K E) :
    Module.finrank K E ∣ Nat.card (ClassGroup (𝓞 K)) := by
  let H := hilbertClassField K (AlgebraicClosure K)
  have hle : (reciprocityMap K H).ker ≤ (reciprocityMap K E).ker := by
    rw [ker_reciprocityMap, range_ideleClassNorm_hilbertClassField]
    rintro _ ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, reciprocityMap_mk]
    apply ideleSymbol_eq_one_of_isUnramifiedEverywhere K E hu
    intro v
    have hx' : x ∈ (Modulus.one : Modulus K).congruenceSubgroup := by
      rw [Modulus.congruenceSubgroup_one]
      exact hx
    have hv := ((Modulus.one : Modulus K).mem_congruenceSubgroup.1 hx').1 v
    rw [(Modulus.exponent_eq_zero_iff _ v).2 (Modulus.not_dvd_one_ideal v)] at hv
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
      (mem_unitsLevel.1 hv).1
  have hd := Subgroup.index_dvd_of_le hle
  rw [rec_index, rec_index] at hd
  rw [Nat.card_congr (hilbertClassFieldArtinEquiv K (AlgebraicClosure K)).toEquiv,
      IsGalois.card_aut_eq_finrank]
  exact hd

end
end Seven.ClassStep

#print axioms Seven.ClassStep.inertia_eq_top_of_normalClosure
#print axioms Seven.ClassStep.prime_quotient_of_proper
#print axioms Seven.ClassStep.cover_group
#print axioms Seven.ClassStep.unramified_degree_dvd
