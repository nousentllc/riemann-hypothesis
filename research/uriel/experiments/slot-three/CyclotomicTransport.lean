import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

noncomputable section

open NumberField UpperTheory.V.Kum

namespace SlotThree.CyclotomicTransport

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev Base := CyclotomicField 3 ℚ
abbrev Layer (n : ℕ) := Fn Base (AlgebraicClosure Base) 3 n
abbrev Standard (n : ℕ) := CyclotomicField (3 ^ n) ℚ

/-- For each positive level the larger order already includes the base field's third roots. -/
theorem rational_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    IsCyclotomicExtension {3 ^ n} ℚ (Layer n) := by
  let _ : IsCyclotomicExtension {3} ℚ Base := CyclotomicField.isCyclotomicExtension 3 ℚ
  let _ : IsCyclotomicExtension {3 ^ n} Base (Layer n) :=
    (fnCyc Base (AlgebraicClosure Base) 3 n).1
  have both := IsCyclotomicExtension.trans ({3} : Set ℕ) {3 ^ n} ℚ Base (Layer n)
    (algebraMap Base (Layer n)).injective
  have hd : 3 ∣ 3 ^ n := by simpa only [pow_one] using (pow_dvd_pow (3 : ℕ) hn)
  apply (IsCyclotomicExtension.iff_union_of_dvd ℚ (Layer n)
    (S := {3 ^ n}) (n := 3) ⟨3 ^ n, rfl, pow_ne_zero n (by decide), hd⟩).2
  rwa [Set.union_comm]

/-- A rational field equivalence with the standard cyclotomic number field. -/
def fieldEquiv (n : ℕ) (hn : 1 ≤ n) : Layer n ≃ₐ[ℚ] Standard n := by
  letI := rational_cyclotomic n hn
  letI : IsCyclotomicExtension {3 ^ n} ℚ (Standard n) :=
    CyclotomicField.isCyclotomicExtension (3 ^ n) ℚ
  exact IsCyclotomicExtension.algEquiv {3 ^ n} ℚ (Layer n) (Standard n)

/-- Field, integer-ring and class-group isomorphisms preserve the reported cardinality. -/
theorem class_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (ClassGroup (𝓞 (Layer n))) = Nat.card (ClassGroup (𝓞 (Standard n))) :=
  Nat.card_congr (ClassGroup.mulEquiv
    (RingOfIntegers.mapRingEquiv (fieldEquiv n hn).toRingEquiv)).toEquiv

/-- The source premise for the regular-prime argument is exactly the standard all-layers premise. -/
theorem all_layers_iff :
    (∀ n : ℕ, 2 ≤ n → ¬ 3 ∣ Nat.card (ClassGroup (𝓞 (Layer n)))) ↔
    (∀ n : ℕ, 2 ≤ n → ¬ 3 ∣ Nat.card (ClassGroup (𝓞 (Standard n)))) := by
  constructor <;> intro h n hn
  · rw [← class_card n (by omega)]
    exact h n hn
  · rw [class_card n (by omega)]
    exact h n hn

#print axioms rational_cyclotomic
#print axioms fieldEquiv
#print axioms class_card
#print axioms all_layers_iff

end SlotThree.CyclotomicTransport
end
