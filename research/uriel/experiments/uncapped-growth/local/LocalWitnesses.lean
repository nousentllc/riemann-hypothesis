import LocalPair
import LocalIsotropy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section

namespace LocalWitnesses

theorem in_pinned_coordinates {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (hM : 3 ≤ M)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) (Fv F v)) (e f : Fin M × Fin d → Fv F v),
      B.IsSymm ∧ B.det ≠ 0 ∧ LocalPair.quad B e = 0 ∧ LocalPair.quad B f = 0 ∧
      f ⬝ᵥ (B *ᵥ e) = 1 ∧
      (∀ (w : Fin M × Fin d → Fv F v) (y : Fv F v),
        LocalPair.quad B (w+y•e) = LocalPair.quad B w + y * (w ⬝ᵥ (B *ᵥ e))) ∧
      ∀ X : Fin 1 → Fin M → Fv F v ⊗[F] E, algebraMap F (Fv F v) (1/2) *
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) =
        LocalPair.quad B (TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) (X 0)) := by
  classical
  obtain ⟨B, X, hB, hd, -, hz, hcov, htrace⟩ := LocalIsotropy.regular_zero σ hσ M J hJ hM d b v
  let Bv := B.map (algebraMap F (Fv F v))
  let c := TraceCoord.coord (Algebra.TensorProduct.basis (Fv F v) b) (M := M)
  let e := c (X 0)
  have hBe : e ⬝ᵥ (Bv *ᵥ e) = 0 := by
    have h := htrace (X 0) (X 0)
    change Algebra.trace _ _ (gramR (Fv F v) σ J X 0 0) = e ⬝ᵥ (Bv *ᵥ e) at h
    simpa [hz] using h.symm
  have hBs := hB.map (algebraMap F (Fv F v))
  have hdv : Bv.det ≠ 0 := (RingHom.map_det (algebraMap F (Fv F v)) B) ▸ (map_ne_zero _).2 hd
  obtain ⟨f, hf, hfe, ha⟩ := LocalPair.partner Bv hBs e hBe hcov
  refine ⟨Bv,e,f,hBs,hdv,by simp [LocalPair.quad,hBe],hf,hfe,ha,?_⟩
  intro Y
  change _ * Algebra.trace _ _ (hR _ _ _ (Y 0) (Y 0)) = _
  rw [htrace]
  simp [LocalPair.quad, Bv, map_ofNat]


/-- Clear all coordinate denominators simultaneously, keeping the multiplier
strictly positive in the original local field. -/
theorem integral_scale {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {I : Type} [Fintype I] (e : I → Fv F v) :
    ∃ a : Fv F v, a ≠ 0 ∧ ∀ i, a * e i ∈ v.adicCompletionIntegers F := by
  classical
  choose n hn hm using fun i => Growth.exists_nat_mul_mem v (e i)
  let N := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hn i)
  refine ⟨(N : Fv F v), by exact_mod_cast hN.ne', ?_⟩
  intro i
  obtain ⟨t, ht⟩ : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [ht, Nat.cast_mul, mul_comm (n i : Fv F v), mul_assoc]
  exact mul_mem (natCast_mem (v.adicCompletionIntegers F) t) (hm i)

/-- Scaling a hyperbolic pair into the specified coordinate lattice can cost
a nonunit Jacobian. Its product stays nonzero, which suffices for a germ. -/
theorem integral_pair {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {I : Type} [Fintype I] [DecidableEq I] (B : Matrix I I (Fv F v)) (hB : B.IsSymm)
    (e f : I → Fv F v) (he : LocalPair.quad B e = 0) (hf : LocalPair.quad B f = 0)
    (hreg : f ⬝ᵥ (B *ᵥ e) ≠ 0) :
    ∃ e' f' : I → Fv F v, (∀ i, e' i ∈ v.adicCompletionIntegers F) ∧
      (∀ i, f' i ∈ v.adicCompletionIntegers F) ∧ LocalPair.quad B f' = 0 ∧
      f' ⬝ᵥ (B *ᵥ e') ≠ 0 ∧ ∀ w y, LocalPair.quad B (w + y • e') =
        (w ⬝ᵥ (B *ᵥ e')) * y + LocalPair.quad B w := by
  obtain ⟨a, ha, hA⟩ := integral_scale v e
  obtain ⟨c, hc, hC⟩ := integral_scale v f
  have he0 : e ⬝ᵥ (B *ᵥ e) = 0 := (mul_eq_zero.mp he).resolve_left (inv_ne_zero two_ne_zero)
  have hf0 : f ⬝ᵥ (B *ᵥ f) = 0 := (mul_eq_zero.mp hf).resolve_left (inv_ne_zero two_ne_zero)
  have he' : (a • e) ⬝ᵥ (B *ᵥ (a • e)) = 0 := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, he0]
  refine ⟨a • e, c • f,hA,hC,?_,?_,?_⟩
  · simp [LocalPair.quad, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, hf0]
  · simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, ha, hc, hreg, smul_eq_mul]
  · intro w y
    rw [LocalPair.along B hB _ he']
    ring

end LocalWitnesses
#print axioms LocalWitnesses.in_pinned_coordinates
#print axioms LocalWitnesses.integral_pair
