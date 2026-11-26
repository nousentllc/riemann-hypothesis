import Mathlib

open scoped BigOperators
namespace GlobalFrobenius
noncomputable section

/-- Cancellation of all full turns in a cyclic orbit. -/
private theorem addOrder_action_mod {A : Type*} [AddCommGroup A] [Finite A] (h : A) (i : ℕ) :
    (i % addOrderOf h) • h = i • h := by
  simp

/-- The actual points in a single dyadic coset have two distinct odd partners
    under one step. The step is a generator of their difference subgroup,
    whose order is at least the number of retained points in the coset. -/
theorem dyadic_coset_two_odd {A : Type*} [AddCommGroup A] [Finite A]
    (T : Finset A) (a₀ : A) {e : ℕ} (hd : addOrderOf a₀ ∣ 2 ^ e)
    (hT : 2 < T.card)
    (hcoset : ∀ a ∈ T, ∀ b ∈ T, b - a ∈ AddSubgroup.zmultiples a₀) :
    ∃ h t : A, ∃ i j : ℕ, T.card ≤ addOrderOf h ∧
      t ∈ T ∧ t + i • h ∈ T ∧ t + j • h ∈ T ∧ Odd i ∧ Odd j ∧ i ≠ j ∧
      i < addOrderOf h ∧ j < addOrderOf h := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let D : Set A := (fun b : A => b - a) '' (T : Set A)
  let K := AddSubgroup.closure D
  have hKA : K ≤ AddSubgroup.zmultiples a₀ := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨b, hb, rfl⟩
    exact hcoset a ha b hb
  obtain ⟨m, hK⟩ := (AddSubgroup.le_zmultiples_iff a₀ K).mp hKA
  let h := m • a₀
  change K = AddSubgroup.zmultiples h at hK
  let n := addOrderOf h
  have hm (b : A) (hb : b ∈ T) : b - a ∈ K := AddSubgroup.subset_closure ⟨b, hb, rfl⟩
  have span (b : A) (hb : b ∈ T) : ∃ i < n, a + i • h = b := by
    have hh := hm b hb
    rw [hK, mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hh
    obtain ⟨i, hi, heq⟩ := hh
    exact ⟨i, Finset.mem_range.mp hi, by rw [heq]; abel⟩
  have hnT : T.card ≤ n := by
    let f : (↥T) → K := fun b => ⟨b.val - a, hm b.val b.property⟩
    have hinj : Function.Injective f := fun b c heq => by
      apply Subtype.ext
      have Heq := congrArg (fun y : K => (y : A)) heq
      simpa [f] using congrArg (fun x : A => x + a) Heq
    have hh := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_coe, ← Nat.card_eq_fintype_card, hK, Nat.card_zmultiples] at hh
    exact hh
  have hnd : n ∣ 2 ^ e := (addOrderOf_dvd_of_mem_zmultiples (hKA (hK ▸ AddSubgroup.mem_zmultiples h))).trans hd
  obtain ⟨v, hv, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hnd
  have hv0 : v ≠ 0 := by
    intro e0
    simp [e0] at hn
    omega
  have hEven : Even n := by
    rw [hn]
    exact even_two.pow_of_ne_zero hv0
  have hOdd : ∃ b ∈ T, ∃ i < n, Odd i ∧ a + i • h = b := by
    by_contra! H
    have hsmall : K ≤ AddSubgroup.zmultiples (2 • h) := by
      apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨j, hj, heq⟩ := span b hb
      have hev : Even j := Nat.not_odd_iff_even.mp (fun ho => H b hb j hj ho heq)
      obtain ⟨k, hk⟩ := hev
      change b - a ∈ AddSubgroup.zmultiples (2 • h)
      rw [← heq, add_sub_cancel_left]
      have hk' : j = 2 * k := by omega
      rw [hk', mul_nsmul]
      exact (AddSubgroup.zmultiples (2 • h)).nsmul_mem (AddSubgroup.mem_zmultiples (2 • h)) k
    have hin : h ∈ AddSubgroup.zmultiples (2 • h) := hsmall (hK ▸ AddSubgroup.mem_zmultiples h)
    have he := (mem_zmultiples_nsmul_iff.mp hin : (2 : ℕ).gcd n = 1)
    have hvd : 2 ∣ Nat.gcd 2 n := Nat.dvd_gcd (by norm_num) hEven.two_dvd
    rw [he] at hvd
    norm_num at hvd
  obtain ⟨b, hb, i, hi, hoi, hab⟩ := hOdd
  have hba : b ≠ a := by
    intro heq
    have zero : i • h = 0 := by
      exact add_left_cancel (show a + i • h = a + 0 by simpa [heq] using hab)
    have hdiv := addOrderOf_dvd_of_nsmul_eq_zero zero
    have hip : 0 < i := hoi.pos
    exact (not_le_of_gt hi) (Nat.le_of_dvd hip hdiv)
  have hE : ((T.erase a).erase b).Nonempty := by
    apply Finset.card_pos.mp
    have c1 := Finset.card_erase_of_mem ha
    have c2 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, hb⟩)
    omega
  obtain ⟨c, hc⟩ := hE
  obtain ⟨hcb, hc'⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca, hcT⟩ := Finset.mem_erase.mp hc'
  obtain ⟨j, hj, hac⟩ := span c hcT
  by_cases hjo : Odd j
  · exact ⟨h, a, i, j, hnT, ha, hab ▸ hb, hac ▸ hcT, hoi, hjo,
           fun hij => hcb (hac.symm.trans (hij ▸ hab)), hi, hj⟩
  · have hjev : Even j := Nat.not_odd_iff_even.mp hjo
    let r := n - i
    have hr : 0 < r ∧ r < n := by dsimp [r]; have := hoi.pos; omega
    have hro : Odd r := by
      rw [Nat.odd_iff] at hoi ⊢
      rw [Nat.even_iff] at hEven
      dsimp [r]
      omega
    have hbr : b + r • h = a := calc
      _ = a + (i + r) • h := by rw [← hab, add_nsmul, add_assoc]
      _ = a := by rw [show i+r=n by dsimp [r]; omega, addOrderOf_nsmul_eq_zero, add_zero]
    let k := (r+j) % n
    have hk : k < n := Nat.mod_lt _ (addOrderOf_pos h)
    have hko : Odd k := by
      have hop : Odd (r+j) := hro.add_even hjev
      rw [Nat.odd_iff] at hop ⊢
      rw [Nat.even_iff] at hEven
      have hsum : r+j < 2*n := by omega
      by_cases hn' : r+j < n
      · simpa [k, Nat.mod_eq_of_lt hn'] using hop
      · have heq : (r+j)%n = r+j-n := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        change (r+j)%n % 2 = 1
        rw [heq]
        omega
    have hbk : b + k • h = c := calc
      _ = b + (r+j) • h := by simp [k,n]
      _ = c := by rw [add_nsmul, ← add_assoc, hbr, hac]
    exact ⟨h, b, r, k, hnT, hb, hbr ▸ ha, hbk ▸ hcT, hro, hko,
      fun heq => hca (hbk.symm.trans (heq ▸ hbr)), hr.2, hk⟩

open Classical in
/-- A bounded number of cyclic cosets forces at least one large retained fiber. -/
theorem exists_coset_above {A : Type*} [AddCommGroup A] [Fintype A]
    (S : AddSubgroup A) (T : Finset A) (k : ℕ) (h : k * S.index < T.card) :
    ∃ c : A ⧸ S, k < (T.filter (fun t => (QuotientAddGroup.mk t : A ⧸ S) = c)).card := by
  classical
  by_contra! H
  have heq : T.card = ∑ c : A ⧸ S, (T.filter (fun t => (QuotientAddGroup.mk t : A ⧸ S) = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hu := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (A ⧸ S))) => H c)
  rw [← heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, mul_comm] at hu
  exact (not_lt_of_ge (show T.card ≤ k * S.index from hu)) h

end
end GlobalFrobenius

#print axioms GlobalFrobenius.dyadic_coset_two_odd
#print axioms GlobalFrobenius.exists_coset_above
