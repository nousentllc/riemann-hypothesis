import SemilinearTransport

open NumberField GroundTheory.Global GroundTheory.ProfCoh IntermediateField
open Ascent.Semi

namespace Ascent.Direct

noncomputable section

/-- Every semilinear automorphism of the ambient field preserves this Hilbert class field. -/
theorem stable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
    [IsTotallyComplex E] (ψ : E ≃+* E) (σ : Ω ≃+* Ω)
    (hc : ∀ x, σ (algebraMap E Ω x) = algebraMap E Ω (ψ x)) (x : Ω)
    (hx : x ∈ hilbertClassField E Ω) : σ x ∈ hilbertClassField E Ω := by
  let H := hilbertClassField E Ω
  let J := tr ψ σ hc H
  have hm := mem_tr ψ σ hc H
  let φ : H ≃+* J := resEquiv σ H J hm
  have hs : ∀ a, φ (algebraMap E H a) = algebraMap E J (ψ a) := resEquiv_algebraMap ψ σ hc H J hm
  have compat : (algebraMap E J).comp ψ.toRingHom = φ.toRingHom.comp (algebraMap E H) :=
    RingHom.ext fun a => (hs a).symm
  let : FiniteDimensional E J := finite_of_resEquiv ψ σ hc H J hm
  let : IsGalois E J := IsGalois.of_equiv_equiv (F := E) (E := H) (f := ψ) (g := φ) compat
  let φG := galEquiv ψ φ hs
  let : IsMulCommutative Gal(J/E) := IsMulCommutative.of_comm fun a b => by
    apply φG.symm.injective
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative Gal(H/E))) _ _
  let : IsAbelianGalois E J := {}
  have hu := isUnramifiedEverywhere_hilbertClassField E Ω
  have away : IsUnramifiedOutside (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) H :=
    fun v _ => hu.1 v
  have same : Corr ψ (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) ∅ := fun v => by simp
  have uj := unram_tr ψ σ hc same away
  apply (le_hilbertClassField_iff E Ω J).2 _ ((hm x).1 hx)
  refine ⟨fun v => uj v (Set.notMem_empty _), fun v w hw => ?_⟩
  apply InfinitePlace.isUnramified_iff.mpr
  right
  rw [hw]
  exact IsTotallyComplex.isComplex v

theorem hilbert_galois (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω]
    [Algebra F Ω] [IsScalarTower F E Ω] [IsAlgClosed Ω] [Normal F Ω]
    [Algebra F (hilbertClassField E Ω)] [IsScalarTower F E (hilbertClassField E Ω)] :
    IsGalois F (hilbertClassField E Ω) := by
  let H := hilbertClassField E Ω
  apply IsGalois.of_fixedField_eq_bot F H
  apply eq_bot_iff.2
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := E) x).2 fun σ =>
    hx (σ.restrictScalars F) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) y).2 fun s => by
    let σ := s.liftNormal Ω
    have hc : ∀ a, σ (algebraMap E Ω a) = algebraMap E Ω (s a) := s.liftNormal_commutes Ω
    have hc' := symm_compat s.toRingEquiv σ.toRingEquiv hc
    have hm : ∀ t : Ω, t ∈ H ↔ σ t ∈ H := fun t => ⟨stable E Ω s.toRingEquiv σ.toRingEquiv hc t, fun h => by
      simpa using stable E Ω s.symm.toRingEquiv σ.symm.toRingEquiv hc' (σ t) h⟩
    let f : H ≃+* H := resEquiv σ.toRingEquiv H H hm
    have hf : ∀ a, f (algebraMap E H a) = algebraMap E H (s a) :=
      resEquiv_algebraMap s.toRingEquiv σ.toRingEquiv hc H H hm
    let g : Gal(H/F) := AlgEquiv.ofRingEquiv (f := f) fun a => by
      rw [IsScalarTower.algebraMap_apply F E H, hf, s.commutes]
    exact (algebraMap E H).injective ((hf y).symm.trans (hx g trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

#print axioms stable
#print axioms hilbert_galois
end
end Ascent.Direct
