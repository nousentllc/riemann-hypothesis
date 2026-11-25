import ExceptionalPrimeCriterion
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open GlobalTheory.CompanionTheory.SW.Growth
open ExceptionalPrimeCriterion Filter
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace NeighborhoodGrowth
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {d : ℕ} {b : Module.Basis (Fin d) F E}
  {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
  {m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)}


/-- A rational prime under the local place tends v-adically to zero under powers,
including ramified and dyadic places. Multiplying the squared power by any fixed scalar
preserves the limit. The statement concerns targets, not continuity of their fiber masses. -/
theorem targets_tend_to_zero (v : HeightOneSpectrum (𝓞 F)) (s : F) :
    Tendsto (fun k : ℕ => algebraMap F (Fv F v) (((rationalPrime v ^ k : ℕ):F)^2*s)) atTop (𝓝 0) := by
  have hmem : ((rationalPrime v : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem _
  have hlt := val_lt_one_of_mem v hmem
  have hsmall : Valued.v ((rationalPrime v : ℕ) : Fv F v) < 1 := by simpa using hlt
  have ht := (Valued.tendsto_zero_pow_of_v_lt_one hsmall).pow 2
  simpa using ht.mul_const (algebraMap F (Fv F v) s)

/-- A punctured-neighborhood floor at only the selected exceptional places suffices
for the whole positive integer cone. No value is prescribed to the singular zero fiber. -/
theorem from_punctured_germs (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 3 ≤ M) (hlam : ∀ v, IsStdV v (lam v))
    (hm : ∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v))

    (β : F) (hβ : β ≠ 0) (hne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0) :
    ∃ (N : ℕ) (B : Finset (HeightOneSpectrum (𝓞 F))), 0 < N ∧
    ((∀ v ∈ B, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 →
      δ ≤ (m v (hermScal (Fv F v) σ z) (latV b v)).toReal) →
      ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 0<t →
      c*((N*t:ℕ):ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤
        ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) (dilSet b v (N*t))).toReal) := by
  classical
  obtain ⟨N,B,hN,heq⟩ := uncapped_iff (b := b) hσ hJ hM hlam hm β hβ hne
  refine ⟨N,B,hN,?_⟩
  intro h
  apply heq.mpr
  let s := (N:F)^2*β
  have hs : s ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hN.ne' : (N:F)≠0)) hβ
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), ∃ δ : ℝ, 0 < δ ∧ (v ∈ B →
      ∀ᶠ z : Fv F v in 𝓝 0, z ≠ 0 → δ ≤ (m v (hermScal (Fv F v) σ z) (latV b v)).toReal) := by
    intro v; by_cases hv : v ∈ B
    · obtain ⟨δ,hδ,hg⟩ := h v hv; exact ⟨δ,hδ,fun _ => hg⟩
    · exact ⟨1,zero_lt_one,fun hh => (hv hh).elim⟩
  choose δ hδ hg using hall
  intro p hp
  let S := B.filter (fun v => rationalPrime v = p)
  have ht (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
      ∀ᶠ k : ℕ in atTop, δ v ≤ (mL σ b m (((p^k:ℕ):F)^2*s) v).toReal := by
    obtain ⟨hvB,hvp⟩ := Finset.mem_filter.mp hv
    subst p
    have eventually := (targets_tend_to_zero v s).eventually (hg v hvB)
    filter_upwards [eventually] with k hk
    apply hk
    apply (map_ne_zero _).2
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (pow_pos (prime_below v).pos k).ne' : ((rationalPrime v^k:ℕ):F)≠0)) hs
  have hsim := (Filter.eventually_all_finset S).mpr ht
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hsim
  exact ⟨K, ∏ v ∈ S, δ v, Finset.prod_pos fun v _ => hδ v,
    fun k hk => Finset.prod_le_prod (fun v _ => (hδ v).le) (hK k hk)⟩
end NeighborhoodGrowth
#print axioms NeighborhoodGrowth.targets_tend_to_zero
#print axioms NeighborhoodGrowth.from_punctured_germs
