import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

open Formalism.BasicNotions Formalism.HC Formalism.MainNotions UpperTheory.Comparison₂
namespace SelectedPlace
noncomputable section

theorem rank_ceiling {R : Ranks} (H : Host R) (hd : H.d = 9239) : R.k ≤ 44 := by
  have hr : R.r + 5 ≤ R.t := by
    have := R.rank_add_five_le
    simpa only [Ranks.r] using this
  have hd_big := H.qd_big.2
  rw [hd] at hd_big
  have hR : R.r ≤ 45 := by
    by_contra! h
    have hT : 51 ≤ R.t := by omega
    have hp := Nat.mul_le_mul hT h
    nlinarith only [hp, hd_big]
  have hm := R.two_le_m
  unfold Ranks.r at hR
  omega

theorem eleven_cannot_supply_host {R : Ranks} (H : Host R) : H.q ≠ 11 := by
  intro hq
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have ht := R.rank_add_five_le
  have hr : 6 ≤ R.r := by unfold Ranks.r; omega
  have hT : 11 ≤ R.t := by omega
  have hp := Nat.mul_le_mul hT hr
  have hq_big := H.qd_big.1
  rw [hq] at hq_big
  nlinarith only [hp, hq_big]

theorem signed_capacity {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    Fintype.card (ℤˣ × R.toFrame.A) ≤ 44 := by
  rw [Fintype.card_prod, Fintype.card_units_int, Frame.card_A]
  exact R.f_le_k.trans (rank_ceiling H hd)

theorem unsigned_capacity {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    Fintype.card R.toFrame.A ≤ 22 := by
  have h := signed_capacity H hd
  rw [Fintype.card_prod, Fintype.card_units_int] at h
  omega

theorem no_signed_injection {S : Type*} [Fintype S] (hS : 44 < Fintype.card S)
    {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    ¬ ∃ f : S → ℤˣ × R.toFrame.A, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact (not_lt_of_ge ((Fintype.card_le_of_injective f hf).trans (signed_capacity H hd))) hS

theorem retained_ceiling {R : Ranks} (H : Host R) (hd : H.d = 9239) : H.TT.card ≤ 22 :=
  (Finset.card_le_univ _).trans (unsigned_capacity H hd)

/-- A lossless embedding forces a lower bound on the host prime for any input size. -/
theorem prime_budget {S : Type*} [Fintype S] {R : Ranks} (H : Host R)
    (f : S → ℤˣ × R.toFrame.A) (hf : Function.Injective f) :
    4 * (Fintype.card S + 6) * (Fintype.card S + 1) + 1 < H.d := by
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_units_int, Frame.card_A] at hcard
  have hk := hcard.trans R.f_le_k
  have hm := R.two_le_m
  have hr : Fintype.card S + 1 ≤ R.r := by unfold Ranks.r; omega
  have ht : Fintype.card S + 6 ≤ R.t := by
    have h_rank := R.rank_add_five_le
    unfold Ranks.r at hr
    omega
  have hprod := Nat.mul_le_mul_left 4 (Nat.mul_le_mul ht hr)
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at hprod
  exact (Nat.succ_le_succ hprod).trans_lt H.qd_big.2

/-- The literal paired consumer uses this very host and this very retained set. -/
theorem consumer_ceiling {eps : ℝ} (F : FamP eps) (n : ℕ) (i : F.Ix (n : ℝ))
    (hd : (F.D n i).host.d = 9239) :
    Fintype.card (ℤˣ × (F.D n i).R.toFrame.A) ≤ 44 ∧ (F.D n i).host.TT.card ≤ 22 :=
  ⟨signed_capacity _ hd, retained_ceiling _ hd⟩

end
end SelectedPlace
#print axioms SelectedPlace.signed_capacity
#print axioms SelectedPlace.no_signed_injection
#print axioms SelectedPlace.retained_ceiling
#print axioms SelectedPlace.eleven_cannot_supply_host
#print axioms SelectedPlace.consumer_ceiling
#print axioms SelectedPlace.prime_budget
