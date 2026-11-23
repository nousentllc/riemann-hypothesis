import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField

noncomputable section

open NumberField GroundTheory.Global IntermediateField
open scoped IsMulCommutative

namespace Seven.Cover

variable (p : ℕ) [Fact p.Prime]

abbrev powers (A : Type*) [CommGroup A] := (powMonoidHom p : A →* A).range

omit [Fact p.Prime] in
theorem powers_characteristic (A : Type*) [CommGroup A] : (powers p A).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro φ x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨φ y, (map_pow φ y p).symm⟩

theorem powers_ne_top (A : Type*) [CommGroup A] [Finite A] (h : p ∣ Nat.card A) :
    powers p A ≠ ⊤ := by
  intro hall
  have hsurj : Function.Surjective (powMonoidHom p : A →* A) := MonoidHom.range_eq_top.mp hall
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p h
  have hone : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  have heq : x = 1 := (Finite.injective_iff_surjective.mpr hsurj) (by simpa using hone)
  rw [heq, orderOf_one] at hx
  exact (Fact.out : Nat.Prime p).ne_one hx.symm

omit [Fact p.Prime] in
theorem quotient_pgroup (A : Type*) [CommGroup A] : IsPGroup p (A ⧸ powers p A) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

variable (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]

abbrev H := hilbertClassField E Ω
abbrev Elementary : IntermediateField E (H E Ω) :=
  fixedField (powers p (Gal(H E Ω/E)))

theorem hilbert_degree : Module.finrank E (H E Ω) = Nat.card (ClassGroup (𝓞 E)) := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (hilbertClassFieldArtinEquiv E Ω).toEquiv).symm

theorem elementary_degree_pos (h : p ∣ Nat.card (ClassGroup (𝓞 E))) :
    1 < Module.finrank E (Elementary p E Ω) := by
  have hcard : p ∣ Nat.card (Gal(H E Ω/E)) :=
    (Nat.card_congr (hilbertClassFieldArtinEquiv E Ω).toEquiv) ▸ h
  have hne := powers_ne_top p _ hcard
  have hr := Nat.card_congr (IsGalois.normalAutEquivQuotient (powers p (Gal(H E Ω/E)))).toEquiv
  rw [IsGalois.card_aut_eq_finrank] at hr
  rw [← hr]
  exact Subgroup.one_lt_index_of_ne_top hne

omit [Fact p.Prime] in
theorem elementary_pgroup : IsPGroup p (Gal(Elementary p E Ω/E)) :=
  (quotient_pgroup p (Gal(H E Ω/E))).of_equiv
    (IsGalois.normalAutEquivQuotient (powers p (Gal(H E Ω/E))))

omit [Fact p.Prime] in
theorem elementary_abelian : IsAbelianGalois E (Elementary p E Ω) :=
  IsAbelianGalois.tower_bot E (Elementary p E Ω) (H E Ω)

omit [Fact p.Prime] in
theorem elementary_unramified : IsUnramifiedEverywhere E (Elementary p E Ω) := by
  have hu := isUnramifiedEverywhere_hilbertClassField E Ω
  let L := Elementary p E Ω
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

omit [Fact p.Prime] in
/-- The fixed field of powers is normal downstairs whenever the entire Hilbert field is. -/
theorem elementary_galois_downstairs (F : Type) [Field F] [NumberField F]
    [Algebra F E] [Algebra F (H E Ω)] [IsScalarTower F E (H E Ω)]
    [IsGalois F E] [IsGalois F (H E Ω)] :
    IsGalois F ((Elementary p E Ω).restrictScalars F) := by
  refine { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable F _ (H E Ω), to_normal := ?_ }
  apply normal_iff_forall_map_le'.mpr
  rintro σ x ⟨y, hy, rfl⟩
  change y ∈ fixedField (powers p (Gal(H E Ω/E))) at hy
  change σ y ∈ fixedField (powers p (Gal(H E Ω/E)))
  rw [mem_fixedField_iff] at hy ⊢
  rintro _ ⟨v, rfl⟩
  let a := conjugateOver σ v
  have ha (t : H E Ω) : σ (a t) = v (σ t) := σ.apply_symm_apply _
  have hb := hy (a ^ p) ⟨a, rfl⟩
  have act (j : ℕ) (t : H E Ω) : (v ^ j) (σ t) = σ ((a ^ j) t) := by
    induction j generalizing t with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (congrArg (v ^ j) (ha t).symm).trans (ih (a t))
  exact (act p y).trans (congrArg σ hb)


end Seven.Cover

#print axioms Seven.Cover.powers_characteristic
#print axioms Seven.Cover.powers_ne_top
#print axioms Seven.Cover.quotient_pgroup
#print axioms Seven.Cover.elementary_degree_pos
#print axioms Seven.Cover.elementary_pgroup
#print axioms Seven.Cover.elementary_abelian
#print axioms Seven.Cover.elementary_unramified
#print axioms Seven.Cover.elementary_galois_downstairs
