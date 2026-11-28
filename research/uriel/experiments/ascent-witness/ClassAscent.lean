import SlotApplication
import NextLayer
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr

noncomputable section

open NumberField UpperTheory.V.Kum UpperTheory.V.Tower

namespace SlotThree.Ascent

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev Cl (K : Type) [Field K] [NumberField K] := ClassGroup (𝓞 K)

section Relative
variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

/-- The relative automorphism acts by transporting each integral ideal. -/
@[instance_reducible] def idealClassAction : MulAction Gal(E/K) (Cl E) where
  smul σ c := clMap σ.toRingEquiv c
  one_smul c := by
    change clMap (RingEquiv.refl E) c = c
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    rw [class_map_mk0]
    congr 1
    exact Subtype.ext (Ideal.map_id I.1)
  mul_smul σ τ c := by
    change clMap (σ * τ).toRingEquiv c = clMap σ.toRingEquiv (clMap τ.toRingEquiv c)
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    rw [class_map_mk0, class_map_mk0, class_map_mk0]
    congr 1
    exact Subtype.ext (Ideal.map_map (I := I.1) (RingOfIntegers.mapRingEquiv τ.toRingEquiv).toRingHom
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom).symm

local instance : MulAction Gal(E/K) (Cl E) := idealClassAction K E

abbrev FixedClasses := MulAction.fixedPoints Gal(E/K) (Cl E)

theorem norm_invariant (σ : Gal(E/K)) (c : Cl E) :
    clNorm K (clMap σ.toRingEquiv c) = clNorm K c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_norm_mk, class_norm_mk]
  congr 1
  exact Subtype.ext (Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv (k := K) σ) I.1)

/-- The coinvariants by a generator are the quotient by all differences σ(c)/c. -/
abbrev difference (σ : Gal(E/K)) : Cl E →* Cl E := clMap σ.toRingEquiv / MonoidHom.id _

def normOnCoinvariants (σ : Gal(E/K)) : (Cl E ⧸ (difference K E σ).range) →* Cl K :=
  QuotientGroup.lift _ (clNorm K) (by
    rintro _ ⟨c, rfl⟩
    change clNorm K (clMap σ.toRingEquiv c / c) = 1
    rw [map_div, norm_invariant]; exact div_self' _)

theorem norm_injective_iff (σ : Gal(E/K)) :
    Function.Injective (normOnCoinvariants K E σ) ↔
      (difference K E σ).range = (clNorm K (K' := E)).ker :=
  QuotientGroup.injective_lift_iff _ _ _

omit [NumberField K] in
theorem fixed_card_eq_coinvariant_card (σ : Gal(E/K))
    (hgen : ∀ τ : Gal(E/K), τ ∈ Subgroup.zpowers σ) :
    Nat.card (FixedClasses K E) = Nat.card (Cl E ⧸ (difference K E σ).range) := by
  rw [← Subgroup.index_eq_card, Subgroup.index_range]
  apply Nat.card_congr
  apply Equiv.subtypeEquivProp
  funext c
  apply propext
  change (∀ τ : Gal(E/K), τ • c = c) ↔ clMap σ.toRingEquiv c / c = 1
  rw [div_eq_one]
  refine ⟨fun h => h σ, fun h τ => ?_⟩
  have hσ : σ ∈ MulAction.stabilizer Gal(E/K) c := h
  exact (Subgroup.zpowers_le.mpr hσ) (hgen τ)

theorem one_step_of_fixed_dvd (hG : IsPGroup 3 Gal(E/K))
    (hfixed : Nat.card (FixedClasses K E) ∣ Nat.card (Cl K)) (hK : ¬ 3 ∣ Nat.card (Cl K)) :
    ¬ 3 ∣ Nat.card (Cl E) := by
  intro h
  exact hK (dvd_trans (Nat.modEq_zero_iff_dvd.mp
    ((hG.card_modEq_card_fixedPoints (Cl E)).symm.trans h.modEq_zero_nat)) hfixed)

theorem one_step_of_norm_injective (σ : Gal(E/K)) (hgen : ∀ τ : Gal(E/K), τ ∈ Subgroup.zpowers σ)
    (hinj : Function.Injective (normOnCoinvariants K E σ)) (hG : IsPGroup 3 Gal(E/K))
    (hK : ¬ 3 ∣ Nat.card (Cl K)) : ¬ 3 ∣ Nat.card (Cl E) := by
  apply one_step_of_fixed_dvd K E hG _ hK
  rw [fixed_card_eq_coinvariant_card K E σ hgen]
  exact Subgroup.card_dvd_of_injective _ hinj

end Relative

/-- A subgroup of a finite p-group that normally generates the group already equals it. -/
theorem inertia_eq_top_of_normalClosure {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) (I : Subgroup G) (h : Subgroup.normalClosure (I : Set G) = ⊤) : I = ⊤ := by
  let _ := hG.isNilpotent
  rcases eq_top_or_exists_le_coatom I with hI | ⟨M, hm, hIM⟩
  · exact hI
  · have : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent (G := G)) hm
    exact (hm.1 ((top_le_iff.mp (h ▸ Subgroup.normalClosure_le_normal (N := M) hIM)))).elim

/-- An inertia subgroup strictly below a finite 3-group fits inside a normal subgroup of
index three. Its fixed field is the possible cyclic cubic obstruction downstairs. -/
theorem cubic_quotient_of_proper {G : Type*} [Group G] [Finite G] (hp : IsPGroup 3 G)
    (I : Subgroup G) (hI : I ≠ ⊤) :
    ∃ M : Subgroup G, I ≤ M ∧ M.Normal ∧ M.index = 3 := by
  obtain ⟨M, hm, hIM⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  let _ := hp.isNilpotent
  have hn := Subgroup.NormalizerCondition.normal_of_coatom M
    (Group.normalizerCondition_of_isNilpotent (G := G)) hm
  refine ⟨M, hIM, hn, ?_⟩
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  obtain ⟨b, hb⟩ := (hp.to_subgroup M).exists_card_eq
  have hlt : b < a := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp
    rw [← ha, ← hb]
    exact lt_of_le_of_ne M.card_le_card_group (fun h => hm.1 (M.eq_top_of_card_eq h))
  have hd : 3 ^ (b + 1) ∣ Nat.card G := ha ▸ pow_dvd_pow _ hlt
  obtain ⟨N, hN, hMN⟩ := Sylow.exists_subgroup_card_pow_succ hd hb
  have hne : M ≠ N := by
    rintro rfl
    rw [hb, pow_succ] at hN
    omega
  have htop := hm.2 N (lt_of_le_of_ne hMN hne)
  rw [htop, Subgroup.card_top, pow_succ, ← hb] at hN
  have he := M.card_mul_index
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (he.trans hN)

/-- Multiply the two genuine extension degrees before applying the p-group criterion. -/
theorem cover_group (F E U : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field U] [NumberField U] [Algebra F E] [Algebra E U] [Algebra F U] [IsScalarTower F E U]
    [IsGalois F U] [IsGalois E U] (hdeg : Module.finrank F E = 3)
    (hp : IsPGroup 3 Gal(U/E)) (hbig : 1 < Module.finrank E U) :
    IsPGroup 3 Gal(U/F) ∧ 3 < Nat.card Gal(U/F) := by
  have hcard : Nat.card Gal(U/F) = 3 * Module.finrank E U := by
    rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank F E U, hdeg]
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  rw [IsGalois.card_aut_eq_finrank] at hm
  refine ⟨IsPGroup.of_card (n := m+1) ?_, ?_⟩
  · rw [hcard, hm, pow_succ']
  · rw [hcard]
    omega

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

open NextLayer NumberField.InfinitePlace Ideal IsCyclotomicExtension.Rat

/-- The degree-six cyclotomic field has a Minkowski bound below 5; 2 is inert and
the prime above 3 is generated by ζ₉ − 1. -/
theorem nine_pid (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {9} ℚ K] :
    IsPrincipalIdealRing (𝓞 K) := by
  let M : ℝ := (4 / Real.pi) ^ nrComplexPlaces K *
    ((Nat.factorial (Module.finrank ℚ K) : ℝ) / (Module.finrank ℚ K : ℝ) ^ (Module.finrank ℚ K) *
      Real.sqrt |(NumberField.discr K : ℝ)|)
  have hm : ⌊M⌋₊ ≤ 4 := by
    have hdeg : Module.finrank ℚ K = 6 := (IsCyclotomicExtension.Rat.finrank 9 K).trans (by decide)
    have hdisc : discr K = -19683 := (discr_prime_pow 3 2 K).trans (by decide)
    have hpl : nrComplexPlaces K = 3 := (nrComplexPlaces_eq_totient_div_two 9 (K := K)).trans (by decide)
    have hs : Real.sqrt 19683 ≤ 141 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have hp : 4 / Real.pi ≤ 40 / 31 := (div_le_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_d2])
    apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt' (by decide : 5 ≠ 0)).2
    dsimp [M]
    rw [hdeg, hdisc, hpl]
    rw [show |(((-19683 : ℤ) : ℝ))| = 19683 by norm_num]
    change (4 / Real.pi)^3 * ((720 : ℝ) / 6^6 * Real.sqrt 19683) < 5
    calc
      _ ≤ (40 / 31 : ℝ) ^ 3 * (720 / 6 ^ 6 * 141) := by gcongr
      _ < 5 := by norm_num
  have horder : orderOf (2 : ZMod 9) = 6 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, fun m hm hp => ?_⟩
    interval_cases m <;> decide
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp prime P hP hpN
  change p ^ P.inertiaDeg ℤ ≤ ⌊M⌋₊ at hpN
  obtain ⟨hprime, hlies⟩ := hP
  have hsmall : p ≤ 4 := (Finset.mem_Icc.mp hp).2.trans hm
  have hcases : p = 2 ∨ p = 3 := by interval_cases p <;> norm_num at *
  rcases hcases with rfl | rfl
  · have hf := inertiaDeg_eq_of_not_dvd 2 K P (m := 9) (by decide)
    rw [show (2 : ZMod 9) = (2 : ℕ) from rfl] at horder
    rw [hf, horder] at hpN
    exact (by omega : False).elim
  · have e := eq_span_zeta_sub_one_of_liesOver 3 1 K (IsCyclotomicExtension.zeta_spec 9 ℚ K) P
    rw [e]
    exact ⟨_, rfl⟩



theorem first_step_class_card : Nat.card (Cl (Upper 0)) = 1 := by
  let _ : IsCyclotomicExtension {9} ℚ (Upper 0) := CyclotomicTransport.rational_cyclotomic 2 (by decide)
  have h := NumberField.classNumber_eq_one_iff.mpr (nine_pid (Upper 0))
  simpa only [NumberField.classNumber, Nat.card_eq_fintype_card] using h

theorem first_step_norm_injective (σ : Gal(Upper 0 / Lower 0)) :
    Function.Injective (normOnCoinvariants (Lower 0) (Upper 0) σ) := by
  have := (Nat.card_eq_one_iff_unique.mp first_step_class_card).1
  exact Function.injective_of_subsingleton _

/-- A field-specific remaining premise for each genuine step of the tower. -/
def FixedClassDivisibility : Prop :=
  ∀ k, Nat.card (FixedClasses (Lower k) (Upper k)) ∣ Nat.card (Cl (Lower k))

def CoinvariantNormInjectivity : Prop :=
  ∀ k, ∃ σ : Gal(Upper k / Lower k), (∀ τ, τ ∈ Subgroup.zpowers σ) ∧
    Function.Injective (normOnCoinvariants (Lower k) (Upper k) σ)

theorem fixed_of_norm (h : CoinvariantNormInjectivity) : FixedClassDivisibility := by
  intro k
  obtain ⟨σ, hg, hn⟩ := h k
  rw [fixed_card_eq_coinvariant_card _ _ σ hg]
  exact Subgroup.card_dvd_of_injective _ hn

theorem regular_lower (h : FixedClassDivisibility) (k : ℕ) : ¬ 3 ∣ Nat.card (Cl (Lower k)) := by
  induction k with
  | zero =>
    rw [CyclotomicTransport.class_card 1 (by decide)]
    simpa [CyclotomicTransport.Standard] using BaseField.three_not_dvd_class_card
  | succ k ih =>
    apply one_step_of_fixed_dvd (Lower k) (Upper k) _ (h k) ih
    apply IsPGroup.of_card (n := 1)
    simpa using (step_group k).1

theorem tower_class_hyp (h : FixedClassDivisibility) : TowerClassHyp := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact regular_lower h k

/-- The k=0 norm condition follows from the explicit class-number-one proof above. -/
theorem tower_of_later_norms
    (h : ∀ k, 1 ≤ k → ∃ σ : Gal(Upper k / Lower k), (∀ τ, τ ∈ Subgroup.zpowers σ) ∧
      Function.Injective (normOnCoinvariants (Lower k) (Upper k) σ)) : TowerClassHyp := by
  apply tower_class_hyp
  apply fixed_of_norm
  intro k
  cases k with
  | zero =>
    have := (step_group 0).2
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(Upper 0 / Lower 0))
    exact ⟨σ, hσ, first_step_norm_injective σ⟩
  | succ k => exact h (k + 1) (by omega)

#print axioms cover_group
#print axioms tower_of_later_norms
#print axioms idealClassAction
#print axioms norm_invariant
#print axioms normOnCoinvariants
#print axioms norm_injective_iff
#print axioms fixed_card_eq_coinvariant_card
#print axioms one_step_of_fixed_dvd
#print axioms one_step_of_norm_injective
#print axioms cubic_quotient_of_proper
#print axioms unramified_degree_dvd
#print axioms nine_pid
#print axioms first_step_class_card
#print axioms first_step_norm_injective
#print axioms regular_lower
#print axioms tower_class_hyp

end SlotThree.Ascent
