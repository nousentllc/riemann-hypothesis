import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField

noncomputable section

open NumberField GroundTheory.Global IntermediateField
open scoped IsMulCommutative

namespace Ascent.Upstairs

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev cubes (A : Type*) [CommGroup A] := (powMonoidHom 3 : A →* A).range

theorem cubes_characteristic (A : Type*) [CommGroup A] : (cubes A).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro φ x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨φ y, (map_pow φ y 3).symm⟩

theorem cubes_ne_top (A : Type*) [CommGroup A] [Finite A] (h : 3 ∣ Nat.card A) :
    cubes A ≠ ⊤ := by
  intro hall
  have hsurj : Function.Surjective (powMonoidHom 3 : A →* A) := MonoidHom.range_eq_top.mp hall
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h
  have hone : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have heq : x = 1 := (Finite.injective_iff_surjective.mpr hsurj) (by simpa using hone)
  simp [heq] at hx

theorem quotient_pgroup (A : Type*) [CommGroup A] : IsPGroup 3 (A ⧸ cubes A) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

variable (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]

abbrev H := hilbertClassField E Ω
abbrev Elementary : IntermediateField E (H E Ω) :=
  fixedField (cubes (Gal(H E Ω/E)))

theorem hilbert_degree : Module.finrank E (H E Ω) = Nat.card (ClassGroup (𝓞 E)) := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (hilbertClassFieldArtinEquiv E Ω).toEquiv).symm

theorem elementary_degree_pos (h : 3 ∣ Nat.card (ClassGroup (𝓞 E))) :
    1 < Module.finrank E (Elementary E Ω) := by
  have hcard : 3 ∣ Nat.card (Gal(H E Ω/E)) :=
    (Nat.card_congr (hilbertClassFieldArtinEquiv E Ω).toEquiv) ▸ h
  have hne := cubes_ne_top _ hcard
  have hr := Nat.card_congr (IsGalois.normalAutEquivQuotient (cubes (Gal(H E Ω/E)))).toEquiv
  rw [IsGalois.card_aut_eq_finrank] at hr
  rw [← hr]
  exact Subgroup.one_lt_index_of_ne_top hne

theorem elementary_pgroup : IsPGroup 3 (Gal(Elementary E Ω/E)) :=
  (quotient_pgroup (Gal(H E Ω/E))).of_equiv
    (IsGalois.normalAutEquivQuotient (cubes (Gal(H E Ω/E))))

theorem elementary_abelian : IsAbelianGalois E (Elementary E Ω) :=
  IsAbelianGalois.tower_bot E (Elementary E Ω) (H E Ω)

theorem elementary_unramified : IsUnramifiedEverywhere E (Elementary E Ω) := by
  have hu := isUnramifiedEverywhere_hilbertClassField E Ω
  let L := Elementary E Ω
  change IsUnramifiedEverywhere E L
  refine ⟨fun v P hP hPv => ?_, fun v w hw => ?_⟩
  · obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 (H E Ω))))
    have hov : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hq := ((GroundTheory.ProfCoh.isUnramifiedAt_tower_iff (F := E) (L := L) Q).1
      (hu.1 v Q hQ hov)).1
    have hp : P = Q.under (𝓞 L) := Ideal.over_def Q P
    subst hp
    exact hq
  · obtain ⟨w', rfl⟩ := NumberField.InfinitePlace.comap_surjective (K := H E Ω) w
    rw [InfinitePlace.isUnramified_iff]
    by_cases hv : v.IsReal
    · left
      have hc : w'.comap (algebraMap E (H E Ω)) = v := by
        rw [IsScalarTower.algebraMap_eq E L (H E Ω), InfinitePlace.comap_comp, hw]
      have hr := (InfinitePlace.isUnramified_iff.1 (hu.2 v w' hc)).resolve_right
        (by rw [hc]; exact InfinitePlace.not_isComplex_iff_isReal.2 hv)
      exact hr.comap _
    · right
      rw [hw]
      exact InfinitePlace.not_isReal_iff_isComplex.1 hv


/-- Conjugating an E-linear automorphism by a downstairs automorphism still fixes E. -/
private def conjugateOver {F E T : Type} [Field F] [Field E] [Field T] [Algebra F E]
    [Algebra E T] [Algebra F T] [IsScalarTower F E T] [Normal F E]
    (σ : Gal(T/F)) (τ : Gal(T/E)) : Gal(T/E) :=
  { (σ.toRingEquiv.trans τ.toRingEquiv).trans σ.symm.toRingEquiv with
    commutes' := fun x => by
      change σ.symm (τ (σ (algebraMap E T x))) = _
      rw [← σ.restrictNormal_commutes E x, τ.commutes, σ.restrictNormal_commutes, σ.symm_apply_apply] }

/-- The fixed field of cubes is normal downstairs whenever the entire Hilbert field is. -/
theorem elementary_galois_downstairs (F : Type) [Field F] [NumberField F]
    [Algebra F E] [Algebra F (H E Ω)] [IsScalarTower F E (H E Ω)]
    [IsGalois F E] [IsGalois F (H E Ω)] :
    IsGalois F ((Elementary E Ω).restrictScalars F) := by
  refine { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable F _ (H E Ω), to_normal := ?_ }
  apply normal_iff_forall_map_le'.mpr
  rintro σ x ⟨y, hy, rfl⟩
  change y ∈ fixedField (cubes (Gal(H E Ω/E))) at hy
  change σ y ∈ fixedField (cubes (Gal(H E Ω/E)))
  rw [mem_fixedField_iff] at hy ⊢
  rintro _ ⟨v, rfl⟩
  let a := conjugateOver σ v
  have ha (t : H E Ω) : σ (a t) = v (σ t) := σ.apply_symm_apply _
  have hb := hy (a ^ 3) ⟨a, rfl⟩
  change v (v (v (σ y))) = σ y
  rw [← ha, ← ha, ← ha]
  exact congrArg σ hb


/-- Degree-three downstairs and a 3-group upstairs give a 3-group over the bottom. -/
theorem galois_p_tower {F E T : Type} [Field F] [Field E] [Field T]
    [Algebra F E] [Algebra E T] [Algebra F T] [IsScalarTower F E T]
    [FiniteDimensional F E] [FiniteDimensional E T] [FiniteDimensional F T]
    [IsGalois E T] [IsGalois F T] (h : Module.finrank F E = 3)
    (hp : IsPGroup 3 (Gal(T/E))) : IsPGroup 3 (Gal(T/F)) := by
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [IsGalois.card_aut_eq_finrank] at hk
  apply IsPGroup.of_card (n := k + 1)
  rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank F E T, h, hk, pow_succ, mul_comm]

end Ascent.Upstairs
