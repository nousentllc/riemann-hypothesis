import OriginalFloor
import SingularZero

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace SingularJump

/-- At the singular scalar the original family's lattice-mass function is
necessarily discontinuous. A nonzero sequence of ordinary integral powers
realizes the contradiction to continuity. -/
theorem discontinuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (hM : 3 ≤ M)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M)
      (coordHerm (Fv F v) σ b lam 1) m) :
    ¬ ContinuousAt (fun s => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) 0 := by
  intro hcon
  let g := fun s => (m (hermScal (Fv F v) σ s) (latV b v)).toReal
  obtain ⟨c, hc, hnear⟩ := OriginalFloor.punctured_floor σ hσ M J hJ hM d b v lam hlam m hm
  have hzero := SingularZero.rank_one_origin σ M J v _ _ m hm
  have h0 : g 0 = 0 := by simp [g,hzero]
  change ContinuousAt g 0 at hcon
  have hgc : g 0 < c := by rw [h0]; exact hc
  have hsub : ∀ᶠ z in 𝓝 (0:Fv F v), g z < c := hcon.eventually (Iio_mem_nhds hgc)
  let q := Ideal.absNorm v.asIdeal
  have hq : (q : Fv F v) ≠ 0 := by
    have : 2 ≤ q := Growth.two_le_norm v
    exact_mod_cast (by omega : q ≠ 0)
  have hsmall : Valued.v (q : Fv F v) < 1 := by
    simpa [q] using Growth.val_lt_one_of_mem v (Ideal.absNorm_mem v.asIdeal)
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hsmall
  obtain ⟨k,hk,hsmall⟩ := (ht.eventually (hnear.and hsub)).exists
  exact not_lt_of_ge (hk (pow_ne_zero k hq)) hsmall

end SingularJump
#print axioms SingularJump.discontinuous
