import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions UpperTheory.Comparison₂
noncomputable section
namespace FixedDatumOriginal

/-- A local certificate on precisely the host and TT selected by the original chain. -/
theorem same_set {eps : ℝ} (F : FamP eps) (Λ : Level) (eD eL K cHH eK CL C : ℝ) (n : ℕ)
    (ha : ∀ i : F.Ix (n : ℝ), EAtH Λ (F.D n i).host.toHostRaw (F.D n i).host.TT n eps C)
    (ht : ChainTied F eD eL K cHH eK CL n) :
    ∃ i : F.Ix (n : ℝ), EAtH Λ (F.D n i).host.toHostRaw (F.D n i).host.TT n eps C ∧
      CoreAtH (F.D n i).host.toHostRaw (F.D n i).host.TT eD eL K cHH eK eps n := by
  obtain ⟨i, h⟩ := tiedCore_of_chainTied F eD eL K cHH eK CL n ht
  exact ⟨i, ha i, h⟩

/-- At a late eligible integer the consumer applies both estimates to the same chosen index. -/
theorem late_consumer {eps : ℝ} (F : FamP eps) (Λ : Level) (heps : 0 < eps)
    (eD eL K cHH eK CL : ℝ) (hE : EFamC Λ F.toFamCore) (xT : ℝ)
    (hT : ∀ x ≥ xT, F.toFamCore.Win x → ChainTied F eD eL K cHH eK CL x) :
    ∃ C x0 : ℝ, ∀ n : ℕ, x0 ≤ (n : ℝ) → F.toFamCore.Win n →
      ∃ i : F.Ix (n : ℝ), EAtH Λ (F.D n i).host.toHostRaw (F.D n i).host.TT n eps C ∧
        CoreAtH (F.D n i).host.toHostRaw (F.D n i).host.TT eD eL K cHH eK eps n ∧
        Λ.Gm n ≤ (n : ℝ) ^ ((1 : ℝ)/2 + (eD+eL+7)*eps) := by
  obtain ⟨C,xE,hE⟩ := hE
  obtain ⟨xG,hG⟩ := core_gm Λ eD eL K cHH eK C eps heps
  refine ⟨C,max (max xE xT) xG, ?_⟩
  intro n hn hw
  obtain ⟨i,ha,hb⟩ := same_set F Λ eD eL K cHH eK CL C n
    (hE n (le_trans (le_max_left _ _) (le_of_max_le_left hn)))
    (hT n (le_trans (le_max_right _ _) (le_of_max_le_left hn)) hw)
  exact ⟨i,ha,hb,hG n (le_of_max_le_right hn) _ (F.D n i).host.toHostAx _ ha hb⟩

theorem no_three_in_cyclic_subgroup (φ : Frame) : ¬ 3 ∣ Nat.card φ.A0 := by
  rw [φ.natCard_cyclic_subgroup]
  intro h
  have bad := h.trans φ.cyclic_order_dvd_two_pow
  have := Nat.prime_three.dvd_of_dvd_pow bad
  norm_num at this

/-- A nonempty retained set supported away from one coset cannot pass a sufficiently fine share bound. -/
theorem missed_coset {φ : Frame} {T : Finset φ.A} (ht : T.Nonempty) {γ : φ.A} {δ : ℝ}
    (hmiss : ∀ t ∈ T, t - γ ∉ φ.A0) (htol : δ < φ.lam γ) : ¬ φ.Shares T δ := by
  classical
  intro hs
  have he : (T.filter (fun t => t - γ ∈ φ.A0)) = ∅ := Finset.filter_eq_empty_iff.mpr hmiss
  have h := hs γ
  rw [he] at h
  have hp : (0:ℝ) < T.card := by exact_mod_cast ht.card_pos
  have hl : 0 ≤ φ.lam γ := by unfold Frame.lam; split_ifs <;> positivity
  simp only [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hl hp.le)] at h
  exact (not_le_of_gt htol) ((mul_le_mul_iff_left₀ hp).mp h)

end FixedDatumOriginal
#print axioms FixedDatumOriginal.late_consumer
#print axioms FixedDatumOriginal.same_set
#print axioms FixedDatumOriginal.no_three_in_cyclic_subgroup
#print axioms FixedDatumOriginal.missed_coset
