import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

open Formalism.HC UpperTheory.V
namespace FixedRoster

theorem order_one : ordC PChar.one = 1 := by
  exact orderOf_one

theorem prime_k : pK PChar.one = 7 := by
  let T : Set ℕ := {p | p.Prime ∧ p % 4 = 3 ∧ 7 ≤ p ∧ p.Coprime 1}
  change sInf T = 7
  have hm : 7 ∈ T := by decide
  exact le_antisymm (Nat.sInf_le hm) ((Nat.sInf_mem ⟨7, hm⟩).2.2.1)

theorem prime_one : pOne PChar.one = 3 := by
  unfold pOne
  rw [order_one, prime_k]
  let T : Set ℕ := {p | p.Prime ∧ p ≡ 1 [MOD ordCompl[2] (1 : ℕ)] ∧ p.Coprime 14}
  change sInf T = 3
  have hm : 3 ∈ T := by
    refine ⟨by decide, ?_, by decide⟩
    simp [Nat.factorization_one, Nat.ModEq]
  have hmin := Nat.sInf_mem (show T.Nonempty from ⟨3, hm⟩)
  have hlo := Nat.Prime.two_le hmin.1
  have hne : sInf T ≠ 2 := by
    intro h
    have hc := hmin.2.2
    rw [h] at hc
    exact (by decide : ¬Nat.Coprime 2 14) hc
  exact le_antisymm (Nat.sInf_le hm) (by omega)

theorem seven_mem : 7 ∈ Bchi PChar.one := by
  unfold Bchi
  rw [order_one, prime_k, prime_one]
  have hpos : 0 < hStar PChar.one := NumberField.classNumber_pos _
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  refine ⟨by decide, Nat.mem_primeFactors.mpr ⟨by decide, ?_, ?_⟩⟩
  · change 7 ∣ 7 * hStar PChar.one * 3
    exact dvd_mul_of_dvd_left (dvd_mul_right 7 _) _
  · change 7 * hStar PChar.one * 3 ≠ 0
    positivity

theorem roster_of_class_one (h : hStar PChar.one = 1) :
    Bchi PChar.one = {3, 7} := by
  unfold Bchi
  rw [order_one, prime_k, prime_one, h]
  change insert 3 (((7 * 3 : ℕ).primeFactors).erase 2) = {3, 7}
  rw [Nat.primeFactors_mul (by decide) (by decide),
    Nat.Prime.primeFactors (by decide : Nat.Prime 7),
    Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
  decide

theorem slot_field (l : ℕ) : Lchi PChar.one l = AbF.cyc l := by
  simp [Lchi, PChar.one]

#print axioms order_one
#print axioms prime_k
#print axioms prime_one
#print axioms seven_mem
#print axioms roster_of_class_one
#print axioms slot_field
end FixedRoster
