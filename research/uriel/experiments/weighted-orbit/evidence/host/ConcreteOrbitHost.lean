import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Mathlib.NumberTheory.LucasPrimality
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation

open Formalism.HC Formalism.FrobeniusOrbits Formalism.BasicNotions HostParam.Seam
namespace Uriel.OrbitHost

set_option maxRecDepth 12000

/-- A typed host over this frame can be chosen at split bound zero. -/
theorem cyclic_host_exists (R : Ranks) (he : 2 ≤ R.e) (hinj : Function.Injective R.h)
    (hn : R.n = 2 ^ R.e) (ho : R.o ^ 64 ≤ 2 ^ R.e) {q d : ℕ} (hh : HostHyp q d) (hq3 : q ≠ 3)
    (hbig : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) :
    ∃ H : Host R, H.q = q ∧ H.d = d ∧ H.QS = 2 ^ (R.e + 2) ∧ H.splitBound = 0 := by
  classical
  obtain ⟨A, hq, hd, hQ, _, _, _, hp, hE, hs⟩ :=
    exists_hostAx R.toFrame hinj he hh
  have hQle : A.QS ≤ R.ord ^ 2 := by
    change R.ord = 2 ^ R.e at hn
    rw [hQ, hn, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hF : FieldRows A.toHostRaw 0 := {
    psQ := hp, sqq := hs, QS_exact := hE, QS_le := hQle
    o_pow := ho
    q_ne_three := hq ▸ hq3
    split_small := by intro p prime _ bound; have hp := prime.two_le; omega
    small_le := by
      intro l prime hne divides
      rw [hQ] at divides
      exact False.elim (hne ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).1 (prime.dvd_of_dvd_pow divides))) }
  obtain ⟨c⟩ := nonempty_choices A.toHostRaw
  obtain ⟨D, heq, hb, _⟩ := exists_host R A hF (by simpa only [hq, hd] using hbig) c
  exact ⟨D, (congrArg (fun u : HostAx R.toFrame => u.q) heq).trans hq,
    (congrArg (fun u : HostAx R.toFrame => u.d) heq).trans hd,
    (congrArg (fun u : HostAx R.toFrame => u.QS) heq).trans hQ, hb⟩

/-- Bounded binary exponentiation for the six explicit Lucas certificates. -/
private def powerBits {m : ℕ} : ℕ → ZMod m → ℕ → ZMod m
  | 0, _, _ => 1
  | i+1, a, k => (if k % 2 = 0 then 1 else a) * powerBits i (a*a) (k / 2)

private theorem powerBits_eq {m : ℕ} (i : ℕ) (a : ZMod m) (k : ℕ) (h : k < 2 ^ i) :
    powerBits i a k = a ^ k := by
  induction i generalizing a k with
  | zero =>
    have : k = 0 := by simpa using h
    simp [powerBits, this]
  | succ i ih =>
    rw [pow_succ] at h
    have hh : k / 2 < 2^i := by omega
    rw [powerBits, ih (a*a) (k/2) hh, ← pow_two, ← pow_mul]
    split <;> rename_i parity
    · rw [one_mul]; congr 1; omega
    · rw [← pow_succ']; congr 1; omega

/-- A prime dividing a complete list of prime factors must occur in the list. -/
private theorem factor_found {q : ℕ} (hq : q.Prime) (fs : List ℕ)
    (hp : ∀ f ∈ fs, f.Prime) (hd : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => exact (hq.not_dvd_one hd).elim
  | cons a fs ih =>
    rw [List.prod_cons] at hd
    rcases hq.dvd_mul.1 hd with h | h
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hp a (by simp))).1 h))
    · exact List.mem_cons.mpr (Or.inr (ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)) h))

/-- Verify the prime factors and the order tests in Lucas's criterion. -/
private theorem certify (bits p a : ℕ) (fs : List ℕ)
    (hb : p < 2^bits) (hf : p-1 = fs.prod) (hp : ∀ f ∈ fs, f.Prime)
    (hbig : powerBits bits (a : ZMod p) (p-1) = 1)
    (hsmall : (fs.all (fun f => decide (powerBits bits (a : ZMod p) ((p-1)/f) ≠ 1))) = true) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · simpa only [powerBits_eq _ _ _ ((Nat.sub_le p 1).trans_lt hb)] using hbig
  · intro q hq hd
    have hm := factor_found hq fs hp (hf ▸ hd)
    have hv := of_decide_eq_true ((List.all_eq_true.mp hsmall) q hm)
    simpa only [powerBits_eq _ _ _ ((Nat.div_le_self _ _).trans_lt ((Nat.sub_le p 1).trans_lt hb))] using hv

-- Checked Lucas certificates and finite instances.

private theorem prime2 : Nat.Prime 2 := by norm_num

private theorem prime17 : Nat.Prime 17 := by norm_num

private theorem prime7 : Nat.Prime 7 := by norm_num

private theorem prime8093 : Nat.Prime 8093 := by
  apply certify 13 8093 2 [2, 2, 7, 17, 17] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime7 | exact prime17

private theorem prime16187 : Nat.Prime 16187 := by
  apply certify 14 16187 2 [2, 8093] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact prime2 | exact prime8093

private theorem prime3 : Nat.Prime 3 := by norm_num

private theorem prime1229 : Nat.Prime 1229 := by norm_num

private theorem prime1074266443 : Nat.Prime 1074266443 := by
  apply certify 31 1074266443 2 [2, 3, 3, 3, 1229, 16187] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime1229 | exact prime16187

private theorem prime5 : Nat.Prime 5 := by norm_num

private theorem prime743 : Nat.Prime 743 := by norm_num

private theorem prime1074266551 : Nat.Prime 1074266551 := by
  apply certify 31 1074266551 7 [2, 3, 3, 3, 3, 3, 5, 5, 7, 17, 743] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime5 | exact prime7 | exact prime17 | exact prime743

private theorem prime457 : Nat.Prime 457 := by norm_num

private theorem prime16453 : Nat.Prime 16453 := by
  apply certify 15 16453 2 [2, 2, 3, 3, 457] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime457

private theorem prime233 : Nat.Prime 233 := by norm_num

private theorem prime83 : Nat.Prime 83 := by norm_num

private theorem prime17181966619 : Nat.Prime 17181966619 := by
  apply certify 35 17181966619 2 [2, 3, 3, 3, 83, 233, 16453] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime83 | exact prime233 | exact prime16453

private theorem prime11 : Nat.Prime 11 := by norm_num

private theorem prime113 : Nat.Prime 113 := by norm_num

private theorem prime29 : Nat.Prime 29 := by norm_num

private theorem prime32771 : Nat.Prime 32771 := by
  apply certify 16 32771 2 [2, 5, 29, 113] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime5 | exact prime29 | exact prime113

private theorem prime331 : Nat.Prime 331 := by norm_num

private theorem prime86777609 : Nat.Prime 86777609 := by
  apply certify 27 86777609 3 [2, 2, 2, 331, 32771] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime331 | exact prime32771

private theorem prime17181966583 : Nat.Prime 17181966583 := by
  apply certify 35 17181966583 3 [2, 3, 3, 11, 86777609] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime11 | exact prime86777609

private theorem prime97 : Nat.Prime 97 := by norm_num

private theorem prime1063 : Nat.Prime 1063 := by norm_num

private theorem prime49369 : Nat.Prime 49369 := by
  apply certify 16 49369 13 [2, 2, 2, 3, 11, 11, 17] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime11 | exact prime17

private theorem prime274886295787 : Nat.Prime 274886295787 := by
  apply certify 39 274886295787 3 [2, 3, 3, 3, 97, 1063, 49369] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime97 | exact prime1063 | exact prime49369

private theorem prime61 : Nat.Prime 61 := by norm_num

private theorem prime3449 : Nat.Prime 3449 := by norm_num

private theorem prime6899 : Nat.Prime 6899 := by
  apply certify 13 6899 2 [2, 3449] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact prime2 | exact prime3449

private theorem prime289759 : Nat.Prime 289759 := by
  apply certify 19 289759 3 [2, 3, 7, 6899] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime7 | exact prime6899

private theorem prime6954217 : Nat.Prime 6954217 := by
  apply certify 23 6954217 5 [2, 2, 2, 3, 289759] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime289759

private theorem prime41725303 : Nat.Prime 41725303 := by
  apply certify 26 41725303 3 [2, 3, 6954217] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime6954217

private theorem prime15271460899 : Nat.Prime 15271460899 := by
  apply certify 34 15271460899 2 [2, 3, 61, 41725303] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime61 | exact prime41725303

private theorem prime274886296183 : Nat.Prime 274886296183 := by
  apply certify 39 274886296183 5 [2, 3, 3, 15271460899] (by decide) (by decide) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> first | exact prime2 | exact prime3 | exact prime15271460899

noncomputable def ranks13 : Ranks := {
  (cyclicFrame 13) with
  k := 16384, m := 2, t := 16391, k_even := by decide, m_even := by decide, t_odd := by decide
  two_le_m := by decide, m_add_three_le_k := by decide, rank_add_five_le := by decide
  three_m_lt_t := by decide, m_le_f := by decide, f_le_k := by decide, m_sq_le_N := by decide }

theorem host13_exists : ∃ H : Host ranks13, H.q = 1074266443 ∧ H.d = 1074266551 ∧ H.QS = 32768 ∧ H.splitBound = 0 := by
  have hh : HostHyp 1074266443 1074266551 := ⟨prime1074266443, prime1074266551, by decide, by decide, by norm_num⟩
  exact cyclic_host_exists ranks13 (by decide) (frameCyc_h_injective 13 1) rfl
    (by rw [show ranks13.o = 1 from cyclicFrame_index 13]; decide) hh (by decide) (by decide)
#print axioms host13_exists

noncomputable def ranks15 : Ranks := {
  (cyclicFrame 15) with
  k := 65536, m := 2, t := 65543, k_even := by decide, m_even := by decide, t_odd := by decide
  two_le_m := by decide, m_add_three_le_k := by decide, rank_add_five_le := by decide
  three_m_lt_t := by decide, m_le_f := by decide, f_le_k := by decide, m_sq_le_N := by decide }

theorem host15_exists : ∃ H : Host ranks15, H.q = 17181966619 ∧ H.d = 17181966583 ∧ H.QS = 131072 ∧ H.splitBound = 0 := by
  have hh : HostHyp 17181966619 17181966583 := ⟨prime17181966619, prime17181966583, by decide, by decide, by norm_num⟩
  exact cyclic_host_exists ranks15 (by decide) (frameCyc_h_injective 15 1) rfl
    (by rw [show ranks15.o = 1 from cyclicFrame_index 15]; decide) hh (by decide) (by decide)
#print axioms host15_exists

noncomputable def ranks17 : Ranks := {
  (cyclicFrame 17) with
  k := 262144, m := 2, t := 262151, k_even := by decide, m_even := by decide, t_odd := by decide
  two_le_m := by decide, m_add_three_le_k := by decide, rank_add_five_le := by decide
  three_m_lt_t := by decide, m_le_f := by decide, f_le_k := by decide, m_sq_le_N := by decide }

theorem host17_exists : ∃ H : Host ranks17, H.q = 274886295787 ∧ H.d = 274886296183 ∧ H.QS = 524288 ∧ H.splitBound = 0 := by
  have hh : HostHyp 274886295787 274886296183 := ⟨prime274886295787, prime274886296183, by decide, by decide, by norm_num⟩
  exact cyclic_host_exists ranks17 (by decide) (frameCyc_h_injective 17 1) rfl
    (by rw [show ranks17.o = 1 from cyclicFrame_index 17]; decide) hh (by decide) (by decide)
#print axioms host17_exists


open NumberField Ideal GlobalTheory.EX

theorem chosen_step_eq_artin {R : Ranks} (H : Host R) {p : ℕ} [hp : Fact p.Prime]
    (hc : Nat.Coprime p H.condN) : hPH H p = R.iotaInv (H.art (ZMod.unitOfCoprime p hc)).2 := by
  classical
  let u := ZMod.unitOfCoprime p hc
  have hu : (u : ZMod H.condN) = (p : ZMod H.condN) := ZMod.coe_unitOfCoprime _ _
  have hnp := (hp.out.coprime_iff_not_dvd).1 hc
  let S : Set R.GG := {g | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g}
  have : (span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hS : ∃ g, g ∈ S := by
    obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 H.E) (span {(p : ℤ)})
    have : P.IsPrime := hP.1
    have : P.LiesOver (span {(p : ℤ)}) := hP.2
    obtain ⟨σ,hσ⟩ := (H.der.frob p hnp P).1
    exact ⟨H.galE σ,P,inferInstance,inferInstance,σ,hσ,rfl⟩
  obtain ⟨P,hp₁,hp₂,σ,hσ,he⟩ := Classical.epsilon_spec hS
  have := hp₁
  have := hp₂
  have eq : Classical.epsilon (fun g => g ∈ S) = H.art u := he.symm.trans (((H.der.frob p hnp P).2.1 σ u hu).1 hσ)
  exact congrArg (fun g : R.GG => R.iotaInv g.2) eq
#print axioms chosen_step_eq_artin


private theorem primeq64 : Nat.Prime 236789744721782169152365302750626042756803 := by
  apply lucas_primality 236789744721782169152365302750626042756803 (2 : ZMod 236789744721782169152365302750626042756803)
  · rw [← powerBits_eq 138 _ _ (by decide)]
    decide +kernel
  · intro l hl hd
    have hf : 236789744721782169152365302750626042756803 - 1 = 2 * 89 * 3^82 := by decide
    rw [hf] at hd
    have hcases : l=2 ∨ l=89 ∨ l=3 := by
      rcases hl.dvd_mul.mp hd with h | h
      · rcases hl.dvd_mul.mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h)
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp (hl.dvd_of_dvd_pow h)))
    rcases hcases with rfl | rfl | rfl
    all_goals rw [← powerBits_eq 138 _ _ (by decide)]
    all_goals decide +kernel

private theorem primed64 : Nat.Prime 135688505402369557604164386969459867197719 := by
  apply lucas_primality 135688505402369557604164386969459867197719 (3 : ZMod 135688505402369557604164386969459867197719)
  · rw [← powerBits_eq 137 _ _ (by decide)]
    decide +kernel
  · intro l hl hd
    have hf : 135688505402369557604164386969459867197719 - 1 = 2 * 17 * 3^83 := by decide
    rw [hf] at hd
    have hcases : l=2 ∨ l=17 ∨ l=3 := by
      rcases hl.dvd_mul.mp hd with h | h
      · rcases hl.dvd_mul.mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h)
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl (by norm_num)).mp (hl.dvd_of_dvd_pow h)))
    rcases hcases with rfl | rfl | rfl
    all_goals rw [← powerBits_eq 137 _ _ (by decide)]
    all_goals decide +kernel

noncomputable def ranks64 : Ranks := {
  (cyclicFramePow 64 1) with
  k := 36893488147419103232, m := 2, t := 36893488147419103239, k_even := by decide, m_even := by decide, t_odd := by decide
  two_le_m := by decide, m_add_three_le_k := by decide, rank_add_five_le := by decide
  three_m_lt_t := by decide, m_le_f := by decide, f_le_k := by decide, m_sq_le_N := by decide }

theorem host64_exists : ∃ H : Host ranks64, H.q = 236789744721782169152365302750626042756803 ∧ H.d = 135688505402369557604164386969459867197719 ∧ H.QS = 73786976294838206464 ∧ H.splitBound = 0 := by
  have hh : HostHyp 236789744721782169152365302750626042756803 135688505402369557604164386969459867197719 := ⟨primeq64, primed64, by decide, by decide, by norm_num⟩
  exact cyclic_host_exists ranks64 (by decide) (frameCyc_h_injective 64 (2 ^ 1)) rfl
    (by rw [show ranks64.o = 2^1 from cyclicFramePow_index 64 1 (by decide)]; decide) hh (by decide) (by decide)
#print axioms host64_exists

end Uriel.OrbitHost
