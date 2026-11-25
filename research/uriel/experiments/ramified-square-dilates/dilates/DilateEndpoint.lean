import DilateRecurrence
import DilatePrimitive
import DilateDescent
import DilateLow
import DilateTransport

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW MeasureTheory
open scoped ENNReal
noncomputable section
namespace RamDilate

private theorem base_tail (n : ℕ) :
    256*TargetOne.count 6 (4 : S (n+3)) = 514*den (n+3) := by
  cases n with
  | zero => rw [low3_four]; decide +kernel
  | succ n =>
    cases n with
    | zero => rw [low4_four]; decide +kernel
    | succ n =>
      have h := RamBridge.normalized n
      change 128*TargetOne.count 6 (4 : S (n+5)) = 257*den (n+5) at h
      change 256*TargetOne.count 6 (4 : S (n+5)) = 514*den (n+5)
      omega

/-- All ordinary powers of two starting at 4, at every indicated precision. -/
theorem powers (j n : ℕ) :
    16^(j+2)*TargetOne.count 6 (2^(j+2) : S (n+j+3)) = (2*16^(j+2)+2)*den (n+j+3) :=
  from_strata (fun n t => primitive_multiple _ (by omega) t) imprim_double_nat base_tail
    (by rw [low4_eight]; decide +kernel) j n

/-- The first stable coefficient depth is 2k+1 for positive square dilates. -/
theorem counts (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    256^k*TargetOne.count 6 (4^k : S (n+(2*k+1))) = (2*256^k+2)*den (n+(2*k+1)) :=
  at_square powers k hk n

open RamGlobal (F conjG gb)
open RamPlaceEndpoint (v K H W fam)

/-- Universal mass theorem on the literal original coordinate lattice and place. -/
theorem original (k : ℕ) (hk : 1 ≤ k) (u : (v.adicCompletionIntegers F)ˣ)
    (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    m (hermScal K conjG ((4:K)^k * ((u : v.adicCompletionIntegers F) : K)^2)) (latV gb v) =
      (2+2/256^k:ℝ≥0∞) :=
  DilateTransport.original k ⟨2*k+1,counts k hk⟩ u lam hlam m hm

/-- One family at the named place works simultaneously for all scales and units. -/
theorem realized :
    ∃ lam : Measure K, IsStdV v lam ∧ ∃ m : H → Measure W, fam lam m ∧
      ∀ k : ℕ, 1 ≤ k → ∀ u : (v.adicCompletionIntegers F)ˣ,
        m (hermScal K conjG ((4:K)^k * ((u : v.adicCompletionIntegers F) : K)^2)) (latV gb v) =
          (2+2/256^k:ℝ≥0∞) :=
  DilateTransport.realized (fun k hk => ⟨2*k+1,counts k hk⟩)

/-- The named-place regular fiber at sixteen, with its reduced rational value. -/
theorem sixteen (lam : Measure K) (hlam : IsStdV v lam) (m : H → Measure W) (hm : fam lam m) :
    m (hermScal K conjG 16) (latV gb v) = (65537/32768 : ℝ≥0∞) := by
  have h := original 2 (by decide) 1 lam hlam m hm
  norm_num at h ⊢
  rw [h]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
  norm_num

end RamDilate
#print axioms RamDilate.powers
#print axioms RamDilate.counts
#print axioms RamDilate.original
#print axioms RamDilate.realized
#print axioms RamDilate.sixteen
