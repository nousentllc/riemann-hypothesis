import OriginalCapacity

open Formalism.BasicNotions Formalism.HC

namespace SelectedPlace
noncomputable section

theorem exponent_le_four {R : Ranks} (H : Host R) (hd : H.d = 9239) : R.e ≤ 4 := by
  have hcard := unsigned_capacity H hd
  rw [Frame.card_A] at hcard
  have hpow := R.toFrame.two_pow_le_ord
  by_contra! hn
  have hbig : 2 ^ 5 ≤ 2 ^ R.e := Nat.pow_le_pow_right (by decide) (by omega)
  change 2 ^ R.e ≤ R.ord at hpow
  change R.ord ≤ 22 at hcard
  omega

theorem single_coset {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    R.toFrame.o = 1 := by
  have he := exponent_le_four H hd
  have hcap : 2 ^ R.e ≤ 16 := Nat.pow_le_pow_right (by decide) he
  have hbound := H.o_pow.trans hcap
  have hpos := R.toFrame.o_pos
  by_contra hn
  have ht : 2 ≤ R.toFrame.o := by omega
  have hh : 2 ^ 64 ≤ R.toFrame.o ^ 64 := by gcongr
  have hbad := hh.trans hbound
  norm_num at hbad

theorem full_cyclic_subgroup {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    R.toFrame.A0 = ⊤ := by
  rw [← AddSubgroup.index_eq_one, R.toFrame.index_A0_eq_o, single_coset H hd]

theorem exact_index_order {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    Fintype.card R.toFrame.A = 2 ^ R.e := by
  rw [Frame.card_A, R.toFrame.exponent_eq_index_mul_cyclic_order, single_coset H hd, one_mul]
  apply le_antisymm R.toFrame.cyclic_order_le_two_pow
  have h := R.toFrame.two_pow_le_ord
  rwa [R.toFrame.exponent_eq_index_mul_cyclic_order, single_coset H hd, one_mul] at h

theorem sharper_signed_capacity {R : Ranks} (H : Host R) (hd : H.d = 9239) :
    Fintype.card (ℤˣ × R.toFrame.A) ≤ 32 := by
  rw [Fintype.card_prod, Fintype.card_units_int, exact_index_order H hd]
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (exponent_le_four H hd))

theorem shares_automatic {R : Ranks} (H : Host R) (hd : H.d = 9239)
    (TT : Finset R.toFrame.A) {δ : ℝ} (hδ : 0 ≤ δ) :
    R.toFrame.Shares TT δ := by
  classical
  unfold Frame.Shares
  intro γ
  have hb : 0 ≤ δ * (TT.card : ℝ) := mul_nonneg hδ (by positivity)
  norm_num [Frame.lam, full_cyclic_subgroup H hd, single_coset H hd]
  exact hb

end
end SelectedPlace

#print axioms SelectedPlace.single_coset
#print axioms SelectedPlace.exact_index_order
#print axioms SelectedPlace.sharper_signed_capacity
#print axioms SelectedPlace.shares_automatic
