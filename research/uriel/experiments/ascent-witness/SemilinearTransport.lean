/- Selected transport declarations from the pinned CohomologicalDimensionTopologicalIso module.
The source intervals and local wrapper are authenticated by check_excerpt.py. -/
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
open NumberField IsDedekindDomain GroundTheory.ProfCoh
namespace Ascent.Semi
section Places

variable {R R' : Type*} [CommRing R] [CommRing R']

def placeMap (f : R ≃+* R') (v : HeightOneSpectrum R) : HeightOneSpectrum R' where
  asIdeal := v.asIdeal.comap f.symm
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply v.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : f x ∈ v.asIdeal.comap f.symm := by simpa [Ideal.mem_comap] using hx
    rw [h] at h1
    have h0 : f x = 0 := (Ideal.mem_bot).1 h1
    exact (Ideal.mem_bot).2 ((map_eq_zero_iff f f.injective).1 h0)

def placeEquiv (f : R ≃+* R') : HeightOneSpectrum R ≃ HeightOneSpectrum R' where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv v := HeightOneSpectrum.ext (by
    ext x
    change f.symm (f x) ∈ v.asIdeal ↔ _
    simp)
  right_inv v := HeightOneSpectrum.ext (by
    ext x
    change f (f.symm x) ∈ v.asIdeal ↔ _
    simp)

end Places

theorem isUnramifiedIn_transport {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A]
    [CommRing A'] [Algebra R A] [Algebra R' A'] (f : R ≃+* R') (g : A ≃+* A')
    (h : ∀ r, g (algebraMap R A r) = algebraMap R' A' (f r)) (p : Ideal R)
    (H : Algebra.IsUnramifiedIn A p) : Algebra.IsUnramifiedIn A' (p.comap f.symm) := by
  intro P' hP' hlie
  let P : Ideal A := P'.comap g
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.LiesOver p := ⟨by
    ext r
    have h1 := hlie.over
    have h2 : f r ∈ p.comap f.symm ↔ f r ∈ P'.under R' := by rw [← h1]
    simp only [Ideal.mem_comap, RingEquiv.symm_apply_apply] at h2
    rw [h2, Ideal.under_def]
    change _ ↔ g (algebraMap R A r) ∈ P'
    rw [h]⟩
  have hU : Algebra.FormallyUnramified R (Localization.AtPrime P) := H P this hP
  letI : Algebra R R' := f.toRingHom.toAlgebra
  letI : Algebra R (Localization.AtPrime P') :=
    ((algebraMap R' (Localization.AtPrime P')).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower R R' (Localization.AtPrime P') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hM : Submonoid.map g.toMonoidHom P.primeCompl = P'.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨g.symm y, ?_, by simp⟩
      intro hmem
      apply hy
      simpa [P, Ideal.mem_comap] using hmem
  let E : Localization.AtPrime P ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P) (Localization.AtPrime P') g hM
  let Ea : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime P' :=
    AlgEquiv.ofRingEquiv (f := E) (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime P)]
      simp only [E]
      rw [IsLocalization.ringEquivOfRingEquiv_eq, h]
      exact (IsScalarTower.algebraMap_apply R' A' (Localization.AtPrime P') (f r)).symm)
  haveI := Algebra.FormallyUnramified.of_equiv Ea
  exact Algebra.FormallyUnramified.of_restrictScalars R R' _

section Fields

variable {F F' Ω Ω' : Type*} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω]
  [Algebra F' Ω']

def resEquiv (e : Ω ≃+* Ω') (E : IntermediateField F Ω) (E' : IntermediateField F' Ω')
    (h : ∀ x, x ∈ E ↔ e x ∈ E') : E ≃+* E' where
  toFun x := ⟨e x, (h x).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simpa using y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def tr (ψ : F ≃+* F') (e : Ω ≃+* Ω') (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    (E : IntermediateField F Ω) : IntermediateField F' Ω' :=
  Subfield.toIntermediateField (E.toSubfield.comap e.symm.toRingHom) (fun x => by
    have h1 : e.symm (algebraMap F' Ω' x) = algebraMap F Ω (ψ.symm x) := by
      rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]
    change e.symm (algebraMap F' Ω' x) ∈ E
    rw [h1]
    exact E.algebraMap_mem _)

theorem mem_tr (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω) (x : Ω) :
    x ∈ E ↔ e x ∈ tr ψ e he E := by
  change _ ↔ e.symm (e x) ∈ E
  simp

theorem resEquiv_algebraMap (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω') (h : ∀ x, x ∈ E ↔ e x ∈ E') (x : F) :
    resEquiv e E E' h (algebraMap F E x) = algebraMap F' E' (ψ x) :=
  Subtype.ext (he x)

theorem finite_of_resEquiv (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x)) (E : IntermediateField F Ω)
    (E' : IntermediateField F' Ω') (h : ∀ x, x ∈ E ↔ e x ∈ E') [FiniteDimensional F E] :
    FiniteDimensional F' E' :=
  Module.Finite.of_equiv_equiv ψ (resEquiv e E E' h) (by
    ext x
    exact (congrArg Subtype.val (resEquiv_algebraMap ψ e he E E' h x)).symm)

end Fields

section Galois

variable {F F' L L' : Type*} [Field F] [Field F'] [Field L] [Field L'] [Algebra F L]
  [Algebra F' L']

theorem symm_compat (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (x : F') :
    e.symm (algebraMap F' L' x) = algebraMap F L (ψ.symm x) := by
  rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]

def galMap (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (σ : Gal(L/F)) : Gal(L'/F') :=
  AlgEquiv.ofRingEquiv (f := (e.symm.trans σ.toRingEquiv).trans e) (fun x => by
    change e (σ (e.symm (algebraMap F' L' x))) = _
    rw [symm_compat ψ e he, σ.commutes, he, RingEquiv.apply_symm_apply])

theorem galMap_apply (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) (σ : Gal(L/F)) (y : L') :
    galMap ψ e he σ y = e (σ (e.symm y)) := rfl

def galEquiv (ψ : F ≃+* F') (e : L ≃+* L')
    (he : ∀ x, e (algebraMap F L x) = algebraMap F' L' (ψ x)) : Gal(L/F) ≃* Gal(L'/F') where
  toFun := galMap ψ e he
  invFun := galMap ψ.symm e.symm (symm_compat ψ e he)
  left_inv σ := AlgEquiv.ext fun x => by simp [galMap_apply]
  right_inv σ := AlgEquiv.ext fun x => by simp [galMap_apply]
  map_mul' σ τ := AlgEquiv.ext fun x => by simp [galMap_apply]
end Galois

section NumberFields

variable {F F' Ω Ω' : Type*} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω]
  [Algebra F' Ω']

theorem placeEquiv_symm_map (ψ : F ≃+* F') :
    placeEquiv (RingOfIntegers.mapRingEquiv ψ.symm) =
      (placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm := rfl

def Corr (ψ : F ≃+* F') (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) :
    Prop :=
  ∀ v, v ∈ S ↔ placeEquiv (RingOfIntegers.mapRingEquiv ψ) v ∈ S'

theorem Corr.symm {ψ : F ≃+* F'} {S : Set (HeightOneSpectrum (𝓞 F))}
    {S' : Set (HeightOneSpectrum (𝓞 F'))} (h : Corr ψ S S') : Corr ψ.symm S' S := by
  intro w
  rw [placeEquiv_symm_map, h, Equiv.apply_symm_apply]

theorem unram_tr (ψ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x, e (algebraMap F Ω x) = algebraMap F' Ω' (ψ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} {S' : Set (HeightOneSpectrum (𝓞 F'))} (hS : Corr ψ S S')
    {E : IntermediateField F Ω} (hE : IsUnramifiedOutside S E) :
    IsUnramifiedOutside S' (tr ψ e he E) := by
  intro w hw
  set f := RingOfIntegers.mapRingEquiv ψ with hf
  set v := (placeEquiv f).symm w with hv
  have hvS : v ∉ S := fun h => hw (by
    have h2 : placeEquiv f v ∈ S' := (hS v).1 h
    rwa [hv, Equiv.apply_symm_apply] at h2)
  have hcompat : ∀ r : 𝓞 F, RingOfIntegers.mapRingEquiv (resEquiv e E (tr ψ e he E) (mem_tr ψ e he E))
      (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap (𝓞 F') (𝓞 (tr ψ e he E)) (f r) := fun r =>
    Subtype.ext (Subtype.ext (he (r : F)))
  have h1 := isUnramifiedIn_transport f _ hcompat v.asIdeal (hE v hvS)
  have hw' : v.asIdeal.comap f.symm = w.asIdeal :=
    congrArg HeightOneSpectrum.asIdeal ((placeEquiv f).apply_symm_apply w)
  rwa [hw'] at h1

end NumberFields
end Ascent.Semi
