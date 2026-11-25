import Mathlib
open MeasureTheory MeasurableSpace

namespace DyadicFiber
/-- A shift by h flips the next bit of an odd square when h is a multiple of 4.
    The certificate is an integer multiple of the full next modulus 4h. -/
theorem flip (k y : ℤ) :
    (2*y+1+4*k)^2 - (2*y+1)^2 = 8*k + (16*k)*(y+k) := by ring

/-- Primitive vectors mod 8 have k odd entries; j of the remaining entries
    have square four. Coordinates are ordered. -/
def primitiveCount (b : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 6, ∑ j ∈ Finset.range (7-k),
    if (k+4*j)%8=b then Nat.choose 6 k * Nat.choose (6-k) j * 4^k * 2^(6-k) else 0

theorem base_table : (List.range 8).map primitiveCount =
    [30720,24576,30720,40960,30720,24576,34816,40960] := by decide

/-- Both signs agree with the measured primitive and all-even contributions. -/
def model (t : ℕ) (sign : ℚ) := 1 - sign / 4^(t+1)

theorem recurrence (t : ℕ) (sign : ℚ) :
    model (t+2) sign = 15/16 + (1/16)*model t sign := by
  simp only [model]
  rw [show t+2+1=(t+1)+2 by omega, pow_add]
  ring

theorem determined (f : ℕ → ℚ → ℚ)
    (base0 : ∀ s, f 0 s = model 0 s) (base1 : ∀ s, f 1 s = model 1 s)
    (step : ∀ t s, f (t+2) s = 15/16 + (1/16)*f t s) :
    ∀ t s, f t s = model t s := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro s
    rcases t with _ | t
    · exact base0 s
    rcases t with _ | t
    · exact base1 s
    rw [step, ih t (by omega), recurrence]

theorem parent_average (t : ℕ) : (model t 1 + model t (-1))/2=1 := by
  unfold model
  ring

theorem opposite_children (t : ℕ) : model t 1 < 1 ∧ 1 < model t (-1) := by
  have h : (0:ℚ)<1/4^(t+1) := by positivity
  unfold model
  rw [neg_div]
  constructor <;> linarith

/-- The finite-measure uniqueness step on the target neighborhood. -/
theorem cylinder_extension {X : Type*} [m : MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] (C : Set (Set X)) (hg : m = generateFrom C) (hp : IsPiSystem C)
    (huniv : μ Set.univ = ν Set.univ) (heq : ∀ A ∈ C, μ A = ν A) : μ = ν := by
  exact MeasureTheory.ext_of_generate_finite C hg hp heq huniv

/-- Equality of cylinder masses for a restricted quadratic pushforward gives the
    measurable-set hypothesis required by the source-level open-neighborhood lemma. -/
theorem counted_image_on_open {X Y : Type*} [MeasurableSpace X] [m : MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (L : Set X) (U : Set Y)
    (q : X → Y) (hq : Measurable q) (c : ENNReal)
    (C : Set (Set Y)) (hg : m = generateFrom C) (hp : IsPiSystem C) (hu : Set.univ ∈ C)
    [IsFiniteMeasure (((μ.restrict L).map q).restrict U)]
    (counts : ∀ A ∈ C, (((μ.restrict L).map q).restrict U) A = (c • ν.restrict U) A) :
    ∀ A : Set Y, MeasurableSet A → A ⊆ U →
      μ {x | x ∈ L ∧ q x ∈ A} = c * ν A := by
  have heq := cylinder_extension (((μ.restrict L).map q).restrict U) (c • ν.restrict U)
    C hg hp (counts _ hu) counts
  intro A hA hAU
  have h := congrArg (fun η : Measure Y => η A) heq
  change (((μ.restrict L).map q).restrict U) A = (c • ν.restrict U) A at h
  rw [Measure.restrict_apply hA, Set.inter_eq_self_of_subset_left hAU,
      Measure.map_apply hq hA, Measure.restrict_apply (hq hA),
      Measure.smul_apply, Measure.restrict_apply hA, Set.inter_eq_self_of_subset_left hAU] at h
  rw [Set.inter_comm] at h
  exact h

end DyadicFiber
#print axioms DyadicFiber.base_table
#print axioms DyadicFiber.flip
#print axioms DyadicFiber.determined
#print axioms DyadicFiber.parent_average
#print axioms DyadicFiber.opposite_children
#print axioms DyadicFiber.cylinder_extension

#print axioms DyadicFiber.counted_image_on_open
