import PrimeBlocks
open Filter
namespace ShellThreshold
/-- An upward-closed shell support with a positive tail floor is exactly one
terminal interval, with a positive floor already on that entire interval. -/
theorem classify (f : ℕ → ℝ) (hnext : ∀ k, 0<f k → 0<f (k+1))
    (htail : ∃ d : ℝ, 0<d ∧ ∀ᶠ k : ℕ in atTop, d ≤ f k) :
    ∃ m : ℕ, ∃ b : ℝ, 0<b ∧ (∀ k, 0<f k ↔ m ≤ k) ∧ ∀ k, m ≤ k → b ≤ f k := by
  classical
  obtain ⟨d,hd,he⟩ := htail
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  have h : ∃ k, 0<f k := ⟨K,hd.trans_le (hK _ le_rfl)⟩
  let m := Nat.find h
  have hmon : Monotone (fun k => 0<f k) := monotone_nat_of_le_succ hnext
  have hc (k : ℕ) : 0<f k ↔ m ≤ k := ⟨Nat.find_min' h, fun hmk => hmon hmk (Nat.find_spec h)⟩
  let g (k : ℕ) := if 0<f k then f k else 1
  have hg (k : ℕ) : 0< g k := by dsimp [g]; split <;> positivity
  obtain ⟨c,hc0,hl⟩ := (PrimeBlocks.tail_iff g hg).mpr ⟨K,d,hd,fun k hk =>
    by simpa [g,hd.trans_le (hK k hk)] using hK k hk⟩
  exact ⟨m,c,hc0,hc,fun k hk => by simpa [g,(hc k).mpr hk] using hl k⟩
end ShellThreshold
#print axioms ShellThreshold.classify
