import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartB
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
  Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower
  UpperTheory.V.Two UpperTheory.V.PropA UpperTheory.V.Win UpperTheory.V.LDataCardLeFinrank

noncomputable section
namespace Seven.Descent

/-- Arithmetic input in the original tower, with its actual indexing. -/
def TowerFree (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ p ∣ Nat.card (ClassGroup (𝓞 (Fn F (AlgebraicClosure F) p n)))

/-- Class groups of order prime to p have trivial quotients by p-th powers. -/
theorem quotientBound (p : ℕ) [Fact p.Prime] (A : Type*) [CommGroup A] (h : ¬p ∣ Nat.card A) :
    Nat.card (A ⧸ (powMonoidHom p : A →* A).range) ≤ p ^ 0 := by
  have cop : (Nat.card A).Coprime p := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 h).symm
  rw [MonoidHom.range_eq_top.mpr cop.pow_left_bijective.surjective]
  have := QuotientGroup.subsingleton_quotient_top (G := A)
  simp

theorem moduleZero (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
    (h : TowerFree p F) : Subsingleton (XP p F) := by
  let Ω := AlgebraicClosure F
  have rk : XRk p 1 (cycU p (⊤ : Subgroup (G F Ω))) 0 :=
    infRk F Ω p 1 0 ⊤ one_ne_zero isClosed_univ fun n hn =>
      levelRk F Ω p n 0 hn (quotientBound _ _ (h n hn))
  obtain ⟨π, onto⟩ := genOfRk F Ω p p 0 ⊤ isClosed_univ (rk.of_one p)
  exact ⟨fun a b => by
    obtain ⟨v,rfl⟩ := onto a
    obtain ⟨w,rfl⟩ := onto b
    exact congrArg π (Subsingleton.elim v w)⟩

/-- Original step0 permits negative as well as positive integral twists. -/
theorem layerZero (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
    (h : TowerFree p F) (hmu : HasMuQ p F) (m : ℕ)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer p m F E)
    (j : ℤ) (hj : j ≠ 0) : shaInv E p j = 0 := by
  let : Subsingleton (XP p F) := moduleZero p F h
  obtain ⟨γ,hγ,_,_⟩ := genLevel p F hmu
  rw [UpperTheory.V.Tower.step0 hmu hγ hj m E hE]
  exact Module.length_eq_zero

abbrev L := CyclotomicField 7 ℚ
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ L := CyclotomicField.isCyclotomicExtension 7 ℚ

theorem muSeven : HasMuQ 7 L :=
  ⟨IsCyclotomicExtension.zeta 7 ℚ L, IsCyclotomicExtension.zeta_spec 7 ℚ L⟩

private theorem ker (a : ℕ) : (AbF.cyc 7).ker a ↔ a ≡ 1 [MOD 7] := by
  change (∃ u ∈ (⊥ : Subgroup (ZMod 7)ˣ), (u : ZMod 7) = (a : ZMod 7)) ↔ _
  constructor
  · rintro ⟨u, hu, h⟩
    rw [Subgroup.mem_bot.mp hu] at h
    exact (ZMod.natCast_eq_natCast_iff a 1 7).mp (by simpa using h.symm)
  · intro h
    exact ⟨1, Subgroup.one_mem _, by simpa using ((ZMod.natCast_eq_natCast_iff a 1 7).mpr h).symm⟩

theorem fieldModel : IsAbField (AbF.cyc 7) L := by
  let ζ := IsCyclotomicExtension.zeta 7 ℚ L
  have hz : IsPrimitiveRoot ζ 7 := IsCyclotomicExtension.zeta_spec 7 ℚ L
  refine ⟨7, inferInstance, AlgHom.id ℚ L, ζ, dvd_refl _, hz, ?_⟩
  intro τ a hτ
  rw [ker]
  have hp : ζ ^ a = ζ ↔ a ≡ 1 [MOD 7] := by
    simpa only [← hz.eq_orderOf, pow_one] using
      ((hz.isOfFinOrder (by decide)).pow_eq_pow_iff_modEq (n := a) (m := 1))
  constructor
  · exact fun h => hp.mp (hτ.symm.trans (h ζ))
  · intro hm
    have hfix : τ.toAlgHom = AlgHom.id ℚ L := by
      apply (hz.powerBasis ℚ).algHom_ext
      rw [hz.powerBasis_gen ℚ]
      exact hτ.trans (hp.mpr hm)
    exact fun x => DFunLike.congr_fun hfix x

theorem invariantOnModel (h : TowerFree 7 L) (m : ℕ)
    (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (j : ℤ) (hj : j ≠ 0) : shaInv E 7 j = 0 := by
  obtain ⟨T, _, _, hAlg, hT⟩ := layerex 7 m (by decide) L muSeven
  obtain ⟨f⟩ := abiso (AbF.cyc 7) L F fieldModel hF
  obtain ⟨g⟩ := layeriso 7 m (by decide) L F T E ⟨f⟩ hT hE
  rw [← shaInv_congr g, layerZero 7 L h muSeven m T hT j hj]

/-- The vanishing is an equality of the actual local-to-global kernel submodule. -/
theorem kernelOnModel (h : TowerFree 7 L) (m : ℕ)
    (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω 7)
    (j : ℤ) (hj : j ≠ 0) : Sha D j = ⊥ := by
  apply Submodule.subsingleton_iff_eq_bot.mp
  apply (Module.length_eq_zero_iff (R := ℤ_[7])).1
  change shaLen D j = 0
  rw [shaLen_eq_shaInv, invariantOnModel h m F hF E hE j hj]

theorem zeroOnModel (h : TowerFree 7 L) (m t : ℕ)
    (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (B : ℝ) (hB : 0 ≤ B) : VVat 7 E t B := by
  apply vvat 7 t E (t : ℝ) 0 B (by norm_num) le_rfl (by simpa using hB)
  intro j hj _
  rw [invariantOnModel h m F hF E hE (j:ℤ) (by omega)]
  simp

/-- Zero total length forces both actual eigensummands to have length zero. -/
theorem bothParts (h : TowerFree 7 L) (m : ℕ)
    (F : Type) [Field F] [NumberField F] (hF : IsAbField (AbF.cyc 7) F)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra F E] (hE : IsLayer 7 m F E)
    (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω 7)
    (j : ℕ) (hj : 1 ≤ j) : plusLen D j = 0 ∧ minusLen D j = 0 := by
  have hz : shaLen D (j:ℤ) = 0 := by
    rw [shaLen_eq_shaInv, invariantOnModel h m F hF E hE (j:ℤ) (by omega)]
  rw [shaLen_eq_add (by decide) D j] at hz
  exact add_eq_zero.mp hz

end Seven.Descent
#print axioms Seven.Descent.quotientBound
#print axioms Seven.Descent.moduleZero
#print axioms Seven.Descent.layerZero
#print axioms Seven.Descent.muSeven
#print axioms Seven.Descent.fieldModel
#print axioms Seven.Descent.invariantOnModel
#print axioms Seven.Descent.kernelOnModel
#print axioms Seven.Descent.zeroOnModel
#print axioms Seven.Descent.bothParts
