import ClassAscent
import Mathlib.RingTheory.ClassGroup.ExtendedHom

noncomputable section
open NumberField UpperTheory.V.Kum UpperTheory.V.Tower
open scoped nonZeroDivisors

namespace SlotThree.Ascent
section ClassNorm
variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]

/-- Extending the downstairs norm of an ideal gives the product of all its conjugates. -/
theorem extend_norm_ideal (I : (Ideal (𝓞 E))⁰) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 E)) (Ideal.relNorm (𝓞 K) I.val) =
      ∏ σ : Gal(E/K), I.val.map (RingOfIntegers.mapRingEquiv σ.toRingEquiv) := by
  have hr : orderOf (ClassGroup.mk0 I) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, I.val ^ orderOf (ClassGroup.mk0 I) = Ideal.span {x} := by
    let r := orderOf (ClassGroup.mk0 I)
    have hc : ClassGroup.mk0 (I ^ r) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    exact (ClassGroup.mk0_eq_one_iff _).mp hc |>.principal
  apply pow_left_injective hr
  dsimp only
  rw [← Ideal.map_pow, ← map_pow, hx, Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton,
      ← Finset.prod_pow]
  simp_rw [← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton]
  rw [Ideal.prod_span_singleton]
  congr 2
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 K) K E,
      Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
  rfl

theorem extend_norm_class (c : Cl E) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 E) (clNorm K c) = ∏ σ : Gal(E/K), clMap σ.toRingEquiv c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_norm_mk, ClassGroup.extendedHom_mk0]
  simp_rw [class_map_mk0]
  rw [← map_prod]
  congr 1
  apply Subtype.ext
  rw [Submonoid.coe_finsetProd]
  exact extend_norm_ideal K E I

/-- The fixed classes form a subgroup, allowing the norm restriction to use Lagrange's theorem. -/
def fixedClassSubgroup : Subgroup (Cl E) where
  carrier := {c | ∀ σ : Gal(E/K), clMap σ.toRingEquiv c = c}
  one_mem' _ := map_one _
  mul_mem' ha hb σ := by rw [map_mul, ha, hb]
  inv_mem' ha σ := by rw [map_inv, ha]

theorem norm_injective_on_fixed (hcard : Nat.card Gal(E/K) = 3) (h : ¬ 3 ∣ Nat.card (Cl E)) :
    Function.Injective ((clNorm K).comp (fixedClassSubgroup K E).subtype) := by
  have hc : (Nat.card (Cl E)).Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 h).symm
  intro x y he
  apply Subtype.ext
  apply hc.pow_left_bijective.injective
  have hpow (c : fixedClassSubgroup K E) :
      ClassGroup.extendedHom (𝓞 K) (𝓞 E) (clNorm K c.val) = c.val ^ 3 := by
    rw [extend_norm_class]
    have hfix (σ : Gal(E/K)) : clMap σ.toRingEquiv c.val = c.val := c.property σ
    simp_rw [hfix]
    simp [← Nat.card_eq_fintype_card, hcard]
  change x.val ^ 3 = y.val ^ 3
  rw [← hpow x, ← hpow y]
  exact congrArg (ClassGroup.extendedHom (𝓞 K) (𝓞 E)) he

theorem fixed_card_divides_of_regular (hcard : Nat.card Gal(E/K) = 3)
    (h : ¬ 3 ∣ Nat.card (Cl E)) : Nat.card (FixedClasses K E) ∣ Nat.card (Cl K) := by
  change Nat.card (fixedClassSubgroup K E) ∣ Nat.card (Cl K)
  exact Subgroup.card_dvd_of_injective _ (norm_injective_on_fixed K E hcard h)

omit [IsGalois K E] in
/-- Modulo the generator's differences, every conjugate represents the same class. -/
private theorem conjugate_mod_difference (σ : Gal(E/K)) (hg : ∀ τ : Gal(E/K), τ ∈ Subgroup.zpowers σ)
    (τ : Gal(E/K)) (c : Cl E) :
    QuotientGroup.mk' (difference K E σ).range (clMap τ.toRingEquiv c) =
      QuotientGroup.mk' (difference K E σ).range c := by
  let _ := idealClassAction K E
  let q := QuotientGroup.mk' (difference K E σ).range
  have hfix (a : Cl E) : q (σ • a) = q a :=
    QuotientGroup.eq_iff_div_mem.2 ⟨a, rfl⟩
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hg τ)
  change q ((σ ^ n) • c) = q c
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_smul, hfix, ih]

/-- The finite group of coinvariants also has order prime to 3. A norm-trivial class has
a cube-trivial image there by transfer, and hence maps to the identity there. -/
theorem norm_on_coinvariants_of_regular (σ : Gal(E/K)) (hg : ∀ τ : Gal(E/K), τ ∈ Subgroup.zpowers σ)
    (hcard : Nat.card Gal(E/K) = 3) (h : ¬ 3 ∣ Nat.card (Cl E)) :
    Function.Injective (normOnCoinvariants K E σ) := by
  let D := (difference K E σ).range
  let q := QuotientGroup.mk' D
  have hQ : (Nat.card (Cl E ⧸ D)).Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2
      (fun hd => h (dvd_trans hd D.index_dvd_card))).symm
  rw [norm_injective_iff]
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change clNorm K (clMap σ.toRingEquiv a / a) = 1
    rw [map_div, norm_invariant, div_self']
  · intro c hc
    change clNorm K c = 1 at hc
    apply (QuotientGroup.eq_one_iff (N := D) c).1
    apply hQ.pow_left_bijective.injective
    change q c ^ 3 = 1 ^ 3
    have he := congrArg q (extend_norm_class K E c)
    rw [hc, map_one, map_one, map_prod] at he
    have hinv (τ : Gal(E/K)) : q (clMap τ.toRingEquiv c) = q c :=
      conjugate_mod_difference K E σ hg τ c
    simp_rw [hinv] at he
    simpa [← Nat.card_eq_fintype_card, hcard] using he.symm

omit [IsGalois K E] in
/-- Norm in the other direction after extending a downstairs ideal class. -/
theorem norm_extend_class (c : Cl K) :
    clNorm K (ClassGroup.extendedHom (𝓞 K) (𝓞 E) c) = c ^ Module.finrank K E := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.extendedHom_mk0, class_norm_mk, ← map_pow]
  congr 1
  apply Subtype.ext
  change Ideal.relNorm (𝓞 K) (Ideal.map (algebraMap (𝓞 K) (𝓞 E)) I.val) = I.val ^ _
  rw [Ideal.relNorm_algebraMap, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]

omit [IsGalois K E] in
/-- Downstairs cubing is onto, so every downstairs class is the norm of an extended class. -/
theorem norm_on_coinvariants_surjective (σ : Gal(E/K)) (hd : Module.finrank K E = 3)
    (h : ¬ 3 ∣ Nat.card (Cl K)) : Function.Surjective (normOnCoinvariants K E σ) := by
  intro c
  have hC : (Nat.card (Cl K)).Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 h).symm
  obtain ⟨a, ha⟩ := hC.pow_left_bijective.surjective c
  refine ⟨QuotientGroup.mk (ClassGroup.extendedHom (𝓞 K) (𝓞 E) a), ?_⟩
  change clNorm K (ClassGroup.extendedHom (𝓞 K) (𝓞 E) a) = c
  simpa only [norm_extend_class, hd] using ha

end ClassNorm

open NextLayer

/-- An independently established prime-to-three tower gives the exact fixed-class divisibility. -/
theorem fixed_of_regular_tower (h : TowerClassHyp) : FixedClassDivisibility := by
  intro k
  let _ := step_galois k
  exact fixed_card_divides_of_regular (Lower k) (Upper k) (step_group k).1 (h (k+2) (by omega))

theorem coinvariant_of_regular_tower (h : TowerClassHyp) : CoinvariantNormInjectivity := by
  intro k
  let _ := step_galois k
  let _ := (step_group k).2
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(Upper k / Lower k))
  exact ⟨σ, hσ, norm_on_coinvariants_of_regular _ _ σ hσ (step_group k).1 (h (k+2) (by omega))⟩

theorem norm_equiv_of_regular_tower (h : TowerClassHyp) (k : ℕ) :
    ∃ σ : Gal(Upper k / Lower k), (∀ τ, τ ∈ Subgroup.zpowers σ) ∧
      Function.Bijective (normOnCoinvariants (Lower k) (Upper k) σ) := by
  obtain ⟨σ, hg, hi⟩ := coinvariant_of_regular_tower h k
  let _ := step_galois k
  exact ⟨σ, hg, hi, norm_on_coinvariants_surjective _ _ σ (step_degree k)
    (regular_lower (fixed_of_regular_tower h) k)⟩

theorem fixed_card_eq_lower (h : TowerClassHyp) (k : ℕ) :
    Nat.card (FixedClasses (Lower k) (Upper k)) = Nat.card (Cl (Lower k)) := by
  obtain ⟨σ, hg, hb⟩ := norm_equiv_of_regular_tower h k
  rw [fixed_card_eq_coinvariant_card _ _ σ hg]
  exact Nat.card_congr (Equiv.ofBijective _ hb)

#print axioms norm_equiv_of_regular_tower
#print axioms fixed_card_eq_lower
#print axioms coinvariant_of_regular_tower
#print axioms extend_norm_class
#print axioms fixed_of_regular_tower
end SlotThree.Ascent
