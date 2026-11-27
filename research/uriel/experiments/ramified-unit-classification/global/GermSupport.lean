import NeighborhoodGrowth
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open ExceptionalPrimeCriterion Filter
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GermSupport
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}


/-- A punctured floor for the original lattice masses forces the entire measure
at every nonzero global target to be nonzero at this place. -/
theorem nonzero_at (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (v : HeightOneSpectrum (𝓞 F)) (β : F) (hβ : β ≠ 0)
    (hg : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 →
      δ ≤ (m v (hermScal (Fv F v) σ z) (latV b v)).toReal) :
    m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0 := by
  obtain ⟨δ,hδ,hnear⟩ := hg
  obtain ⟨k,hk⟩ := ((NeighborhoodGrowth.targets_tend_to_zero v β).eventually hnear).exists
  let a := rationalPrime v ^ k
  have ha : 0 < a := pow_pos (prime_below v).pos _
  have hz : algebraMap F (Fv F v) ((a:F)^2*β) ≠ 0 :=
    (map_ne_zero _).2 (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ha.ne' : (a:F)≠0)) hβ)
  have hpos : 0 < (mL σ b m ((a:F)^2*β) v).toReal := hδ.trans_le (hk hz)
  have hloc : mL σ b m ((a:F)^2*β) v ≠ 0 := by
    intro h; rw [h,ENNReal.toReal_zero] at hpos; exact hpos.false
  obtain ⟨e,he,-,-⟩ := exists_exponents (F := F) a ha
  have hid := dil_eq (b := b) hσ hJ hM hlam hm v β a (e v) ha (he v).1 (he v).2
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by have := two_le_norm v; omega : Ideal.absNorm v.asIdeal ≠ 0)
  intro hzero
  rw [hzero] at hid
  exact (mul_ne_zero (pow_ne_zero _ hq) hloc) hid.symm

end GermSupport
#print axioms GermSupport.nonzero_at
