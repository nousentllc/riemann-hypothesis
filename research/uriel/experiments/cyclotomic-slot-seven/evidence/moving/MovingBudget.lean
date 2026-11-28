import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V
  UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win
namespace Seven.Moving

/-- The original even comparison loses one unit per active integer. This lemma
keeps the exact size of the interval [1,t), including an empty interval. -/
theorem fromComparison (E L₁ : Type) [Field E] [NumberField E] [Field L₁] [NumberField L₁]
    (t H : ℕ) (B : ℝ)
    (cmp : ∀ k : ℕ, 1 ≤ k → k < t → shaInv E 2 k ≤ 1 + shaInv L₁ 2 k)
    (cap : ∀ k : ℕ, 1 ≤ k → k < t → shaInv L₁ 2 k ≤ (H : ℕ∞))
    (budget : ((t - 1 : ℕ) : ℝ) * (1 + H) ≤ B) : VVat 2 E t B := by
  have bounds (k : ℕ) (h : 1 ≤ k) (ht : k < t) :
      shaInv E 2 k ≠ ⊤ ∧ (shaInv E 2 k).toNat ≤ 1+H := by
    have hh : shaInv E 2 k ≤ ((1+H : ℕ) : ℕ∞) := by
      push_cast
      exact (cmp k h ht).trans (add_le_add (le_refl (1:ℕ∞)) (cap k h ht))
    have fin := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hh
    obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp fin
    refine ⟨fin, ?_⟩
    rw [← hm] at hh ⊢
    simp only [ENat.toNat_natCast]
    exact_mod_cast hh
  intro Ω _ _ _ D
  refine ⟨fun k hk ht => ?_,?_⟩
  · rw [shaLen_eq_shaInv]
    exact (bounds k hk ht).1
  calc ∑ k ∈ Finset.Ico 1 t, ((shaLen D (k : ℤ)).toNat : ℝ) ≤ ∑ _k ∈ Finset.Ico 1 t, (1+(H:ℝ)) := by
         apply Finset.sum_le_sum
         intro k hk
         rw [shaLen_eq_shaInv]
         exact_mod_cast (bounds k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2).2
       _ = ((t-1 : ℕ) : ℝ)*(1+H) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
       _ ≤ B := budget

/-- The comparison and bound must belong to one layer. A different tuple can be
chosen for each compositum model, but cannot be exchanged partway through the proof. -/
theorem baAtMatched (M : AbF) (eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ)
    (L₀ : Type) [Field L₀] [NumberField L₀] (H : ℕ)
    (found : ∀ (E : Type) [Field E] [NumberField E], IsCompField M (e x) q d E →
      ∃ (m : ℕ) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁),
        IsLayer 2 m L₀ L₁ ∧ m ≤ e x+2 ∧
        (∀ k : ℕ, 1 ≤ k → k < t x → shaInv E 2 k ≤ 1 + shaInv L₁ 2 k) ∧
        ∀ k : ℕ, 1 ≤ k → k < t x → shaInv L₁ 2 k ≤ (H : ℕ∞))
    (budget : ((t x-1 : ℕ) : ℝ)*(1+H) ≤ Real.exp (x^(4*eps/5))) :
    BaAt M eps e t q d x := by
  intro E _ _ comp
  obtain ⟨m,L₁,_,_,_,_,_,cmp,h⟩ := found E comp
  exact fromComparison E L₁ (t x) H _ cmp h budget

/-- Original TwoBase chooses the comparison layer. A uniform cap can be applied
after that choice. Extraction of its numerical value is a separate obligation. -/
theorem baAtFromTwoBase (M : AbF) (eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ)
    (L₀ : Type) [Field L₀] [NumberField L₀] (H : ℕ) (two : TwoBase M q d L₀)
    (page : 2 ≤ e x)
    (all : ∀ m : ℕ, ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
      IsLayer 2 m L₀ L₁ → m ≤ e x+2 →
      ∀ k : ℕ, 1 ≤ k → k < t x → shaInv L₁ 2 k ≤ (H : ℕ∞))
    (budget : ((t x-1 : ℕ) : ℝ)*(1+H) ≤ Real.exp (x^(4*eps/5))) :
    BaAt M eps e t q d x := by
  apply baAtMatched M eps e t q d x L₀ H _ budget
  intro E _ _ hE
  obtain ⟨m,L₁,_,_,_,hL,hm,cmp⟩ := two.2.2.2 (e x) page E hE
  exact ⟨m,L₁,_,_,_,hL,hm,fun k hk _ => cmp k hk, all m L₁ hL hm⟩

#print axioms fromComparison
#print axioms baAtMatched
#print axioms baAtFromTwoBase
end Seven.Moving
