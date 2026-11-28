import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace Uriel.ServedPrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

private theorem primitive_single {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) :
    ∃ χ : DirichletCharacter ℂ r, χ.IsPrimitive ∧ χ ≠ 1 ∧
      ∀ a : ℕ, χ (a : ZMod r) = QH.J r a := by
  have h := QH.twist_prim 1 r (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one hr h2 hr.not_dvd_one
  let S := fun N : ℕ => ∃ χ : DirichletCharacter ℂ N, χ.IsPrimitive ∧ χ ≠ 1 ∧
    ∀ a : ℕ, χ (a : ZMod N) = QH.J r a
  have hS : S (1 * r) := by
    obtain ⟨χ, hp, hn, hv⟩ := h
    refine ⟨χ, hp, hn, fun a => ?_⟩
    rw [hv, Subsingleton.elim (a : ZMod 1) 1, map_one, one_mul]
  exact (congrArg S (Nat.one_mul r)).mp hS

private theorem kron_on_unit {r a B : ℕ} (hr : r % 4 = 3) (h2 : 2 ∣ B) (ha : a.Coprime B) :
    kron (-(r : ℤ)) a = QH.J r a := by
  have hodd := Nat.odd_iff.mp (Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right h2 ha))
  have hnd : ¬ 2 ∣ a := by omega
  simp [kron, kronSym, QH.J, Nat.factorization_eq_zero_of_not_dvd hnd,
    Formalism.HC.jacobi_neg_recip hr hodd]

/-- Exact moduli and full natural-number evaluations, including prime powers.
    The induction agreements use the units required in the host boxes. -/
theorem three_representatives (D : D7) :
    ∃ (χq : DirichletCharacter ℂ D.host.q) (χd : DirichletCharacter ℂ D.host.d)
        (χdq : DirichletCharacter ℂ (D.host.q * D.host.d)),
      (χq ≠ 1 ∧ χd ≠ 1 ∧ χdq ≠ 1) ∧
      Induces χq (psDir D.host.q) (8 * D.host.q * D.host.d) ∧
      Induces χd (chDir D.host.d) (8 * D.host.q * D.host.d) ∧
      Induces χdq (fun a => chDir D.host.d a * psDir D.host.q a) (8 * D.host.q * D.host.d) ∧
      ∀ a : ℕ, χq (a : ZMod _) = QH.J D.host.q a ∧
        χd (a : ZMod _) = QH.J D.host.d a ∧ χdq (a : ZMod _) = χq (a : ZMod _) * χd (a : ZMod _) := by
  obtain ⟨χq, hq, hnq, hvq⟩ := primitive_single D.host.q_prime D.host.q_ne_two
  obtain ⟨χd, hd, hnd, hvd⟩ := primitive_single D.host.d_prime D.host.d_ne_two
  have : NeZero D.host.q := ⟨D.host.q_prime.ne_zero⟩
  have hdq : ¬ D.host.d ∣ D.host.q := fun h =>
    D.host.q_ne_d ((Nat.prime_dvd_prime_iff_eq D.host.d_prime D.host.q_prime).mp h).symm
  obtain ⟨χdq, hqd, hnqd, hvqd⟩ := QH.twist_prim D.host.q D.host.d χq hq
    D.host.d_prime D.host.d_ne_two hdq
  have h2 : 2 ∣ 8 * D.host.q * D.host.d := ⟨4 * D.host.q * D.host.d, by ring⟩
  refine ⟨χq, χd, χdq, ⟨hnq, hnd, hnqd⟩, ⟨hq, ?_⟩, ⟨hd, ?_⟩, ⟨hqd, ?_⟩, ?_⟩
  · intro a ha
    exact (hvq a).trans (kron_on_unit D.host.q_mod_four h2 ha).symm
  · intro a ha
    exact (hvd a).trans (kron_on_unit D.host.d_mod_four h2 ha).symm
  · intro a ha
    change χdq (a : ZMod _) = chDir D.host.d a * psDir D.host.q a
    rw [hvqd, hvq, chDir, psDir, kron_on_unit D.host.d_mod_four h2 ha,
      kron_on_unit D.host.q_mod_four h2 ha, mul_comm]
  · intro a
    exact ⟨hvq a, hvd a, by rw [hvqd, hvd]⟩

#print axioms three_representatives
end Uriel.ServedPrime
