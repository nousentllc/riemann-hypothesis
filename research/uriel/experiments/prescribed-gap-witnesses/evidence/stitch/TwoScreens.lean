import Mathlib

namespace FirstGap

/-- An active-weight screen, with the allowance argument already evaluated. -/
def Screen (E : Finset ℕ) (t : ℕ) (s : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < t → k ∈ E → (k : ℝ) ≤ s

/-- After a successful earlier test, only integers newly entering the cutoff
can cause a one-sided failure, and every such integer is already too large. -/
theorem leftFailure {E : Finset ℕ} {ta tx : ℕ} {sa sx sb : ℝ}
    (hA : Screen E ta sa) (hax : sa ≤ sx) (hxb : sx ≤ sb) (hcross : sb < (ta : ℝ)) :
    (¬ Screen E tx sx) ↔ ∃ k ∈ E, 1 ≤ k ∧ ta ≤ k ∧ k < tx := by
  classical
  constructor
  · intro h
    unfold Screen at h
    push Not at h
    obtain ⟨k,h1,ht,hE,hs⟩ := h
    refine ⟨k,hE,h1,?_,ht⟩
    by_contra! hk
    exact (not_lt_of_ge ((hA k h1 hk hE).trans hax)) hs
  · rintro ⟨k,hE,h1,hk,ht⟩ s
    have h : (ta : ℝ) ≤ k := by exact_mod_cast hk
    exact (not_lt_of_ge (s k h1 ht hE)) (hxb.trans_lt (hcross.trans_le h))

/-- After a successful later test, every would-be harmful active integer of
that later cutoff is already foreseen by the current cutoff. -/
theorem rightFailure {E : Finset ℕ} {ta tx tb : ℕ} {sx sb : ℝ}
    (hB : Screen E tb sb) (hax : ta ≤ tx) (hxb : tx ≤ tb) (hcross : sb < (ta : ℝ)) :
    (¬ Screen E tx sx) ↔ ∃ k ∈ E, 1 ≤ k ∧ k < tb ∧ sx < k := by
  classical
  constructor
  · intro h
    unfold Screen at h
    push Not at h
    obtain ⟨k,h1,ht,hE,hs⟩ := h
    exact ⟨k,hE,h1,ht.trans_le hxb,hs⟩
  · rintro ⟨k,hE,h1,ht,hs⟩ s
    have h : (k : ℝ) < ta := (hB k h1 ht hE).trans_lt hcross
    have hk : k < ta := by exact_mod_cast h
    exact (not_lt_of_ge (s k h1 (hk.trans_le hax) hE)) hs

/-- Certificate on arbitrary closed availability domains with one left/right
frontier, in an ordered coordinate in which the two boundaries can be
compared exactly. The left endpoint fails at its activation coordinate;
the right endpoint passes at its clearance coordinate. -/
theorem clippedIff {a b l r cl cr : ℝ} (hcl : a ≤ cl) (hcr : cr ≤ b) (har : a ≤ l) (hrb : r ≤ b) :
    (∀ x ∈ Set.Icc a b, (x ≤ cl ∧ x < l) ∨ (cr ≤ x ∧ r ≤ x)) ↔
    max r cr ≤ min l cl := by
  constructor
  · intro cover
    by_contra! h
    let x := (min l cl + max r cr)/2
    have hl : a ≤ min l cl := le_min har hcl
    have hh : max r cr ≤ b := max_le hrb hcr
    have hx : x ∈ Set.Icc a b := ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
    rcases cover x hx with ⟨h1,h2⟩|⟨h1,h2⟩
    · have hm : x ≤ min l cl := le_min h2.le h1
      dsimp [x] at hm
      linarith
    · have hm : max r cr ≤ x := max_le h2 h1
      dsimp [x] at hm
      linarith
  · intro h x _
    by_cases hh : max r cr ≤ x
    · exact Or.inr ⟨(le_max_right _ _).trans hh,(le_max_left _ _).trans hh⟩
    · have hx := lt_of_not_ge hh
      have hx' := hx.trans_le h
      exact Or.inl ⟨(hx'.trans_le (min_le_right _ _)).le,hx'.trans_le (min_le_left _ _)⟩

#print axioms FirstGap.leftFailure
#print axioms FirstGap.rightFailure
#print axioms FirstGap.clippedIff
end FirstGap
