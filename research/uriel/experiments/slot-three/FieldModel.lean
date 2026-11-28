import BaseField
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField UpperTheory.V

namespace SlotThree.FieldModel

abbrev K := SlotThree.BaseField.K
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem ker (a : ℕ) : (AbF.cyc 3).ker a ↔ a ≡ 1 [MOD 3] := by
  change (∃ u ∈ (⊥ : Subgroup (ZMod 3)ˣ), (u : ZMod 3) = (a : ZMod 3)) ↔ _
  constructor
  · rintro ⟨u, hu, h⟩
    rw [Subgroup.mem_bot.mp hu] at h
    exact (ZMod.natCast_eq_natCast_iff a 1 3).mp (by simpa using h.symm)
  · intro h
    exact ⟨1, Subgroup.one_mem _, by simpa using ((ZMod.natCast_eq_natCast_iff a 1 3).mpr h).symm⟩

theorem hasMu : (AbF.cyc 3).HasMu 3 := ⟨dvd_refl 3, fun a => (ker a).mp⟩

/-- Exhibit this precise cyclotomic field as a model of the original character slot. -/
theorem fieldModel : IsAbField (AbF.cyc 3) K := by
  let ζ := IsCyclotomicExtension.zeta 3 ℚ K
  have hz : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  refine ⟨3, inferInstance, AlgHom.id ℚ K, ζ, dvd_refl _, hz, ?_⟩
  intro τ a hτ
  rw [ker]
  have hp : ζ ^ a = ζ ↔ a ≡ 1 [MOD 3] := by
    simpa only [← hz.eq_orderOf, pow_one] using
      ((hz.isOfFinOrder (by decide)).pow_eq_pow_iff_modEq (n := a) (m := 1))
  constructor
  · exact fun h => hp.mp (hτ.symm.trans (h ζ))
  · intro hm
    have hfix : τ.toAlgHom = AlgHom.id ℚ K := by
      apply (hz.powerBasis ℚ).algHom_ext
      rw [hz.powerBasis_gen ℚ]
      exact hτ.trans (hp.mpr hm)
    exact fun x => DFunLike.congr_fun hfix x

end SlotThree.FieldModel
