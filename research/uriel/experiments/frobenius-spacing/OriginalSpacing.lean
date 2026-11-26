import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.GlobalTheoryTheory GlobalTheory.EX
open scoped BigOperators

namespace FrobeniusSpacing
noncomputable section

/-- The fixed discriminant fails the actual selector rank identity, at every scale. -/
theorem rank_identity_prime_floor {R : Ranks} (H : Host R) (s : Scale)
    (h : RankVal s R) : 94897 < H.d := by
  have hmN := R.two_le_m
  have hkN := R.m_add_three_le_k
  have hfN : 2 ≤ R.f := hmN.trans R.m_le_f
  have hrN : 6 ≤ R.r := by unfold Ranks.r; omega
  have hm : (2 : ℝ) ≤ R.m := by exact_mod_cast hmN
  have hk : (R.m : ℝ) + 3 ≤ R.k := by exact_mod_cast hkN
  have hf : (2 : ℝ) ≤ R.f := by exact_mod_cast hfN
  have hL : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le
  have hL2 : 1 ≤ s.L ^ 2 := by nlinarith only [hL, sq_nonneg (s.L - 1)]
  have hk4 : 4 ≤ (R.k : ℝ) - 1 := by linarith
  have hk2 : 16 ≤ ((R.k : ℝ) - 1) ^ 2 := by nlinarith only [hk4, sq_nonneg ((R.k : ℝ) - 5)]
  have hk3 : 16 * (R.m : ℝ) ≤ ((R.k : ℝ) - 1) ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_right hk2 (show 0 ≤ (R.k : ℝ) - 1 by linarith)
    nlinarith only [h1, hk]
  have hf2 : 4 ≤ (R.f : ℝ) ^ 2 := by nlinarith only [hf, sq_nonneg ((R.f : ℝ) - 2)]
  have hq : 64 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    apply (le_div_iff₀ (by linarith : 0 < (R.m : ℝ))).mpr
    have h1 := mul_le_mul_of_nonneg_left hk3 (sq_nonneg (R.f : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hf2 (show 0 ≤ 16 * (R.m : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hL2
      (show 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 by positivity)
    nlinarith only [h1, h2, h3]
  have hW : 660 * R.r ≤ nWv R s := by
    have hc := Nat.le_ceil
      (10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8)
    have hd := mul_le_mul_of_nonneg_left (show 66 ≤ (R.f : ℝ) +
       (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m by linarith)
       (show 0 ≤ (R.r : ℝ) by positivity)
    have hcast : (660 * R.r : ℝ) ≤ (nWv R s : ℝ) := by
      unfold nWv
      push_cast
      nlinarith only [hc, hd]
    exact_mod_cast hcast
  have hto : 1 ≤ TOv s := Nat.ceil_pos.mpr
    (Real.rpow_pos_of_pos (zero_lt_one.trans s.one_lt_alt) _)
  have hW' := Nat.mul_le_mul_right (nWv R s) hto
  have ht : 3954 ≤ R.t := by
    have hh := h.2.2.2
    nlinarith only [hh, hW, hW', hrN]
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 4 ht) hrN
  exact (show 94897 ≤ 4 * R.t * R.r + 1 by omega).trans_lt H.qd_big.2

/-- Even a host satisfying the fixed prime condition cannot be fed to topsChoiceH
    with the scale-tied ranks required by the theorem. -/
theorem no_fixed_rank_val {R : Ranks} (H : Host R) (s : Scale) (hd : H.d = 9239) :
    ¬ RankVal s R := by
  intro h
  have hf := rank_identity_prime_floor H s h
  omega

/-- An inert prime has the same unsigned step in the selector and in the consumer. -/
theorem inert_step_and_partner {R : Ranks} (H : Host R) (s : Scale) (p : ℕ)
    (hp : (baseOf s 0 0 H).IsResidueClassZero p) (t : R.A) (e : ℕ) :
    let B := baseOf s 0 0 H
    let h := hPH H p
    Arith.Loc.stepP B h p = h ∧
      Arith.Loc.partner B h p t e = (false, t + e • h) := by
  have hn : ¬ (baseOf s 0 0 H).IsSg p := by
    unfold Arith.Base.IsSg Arith.Base.IsResidueClassZero at *
    rw [hp]
    decide
  simp [Arith.Loc.stepP, Arith.Loc.partner, hn]

/-- Filter the exact old retained set along one orbit, starting at the supplied anchor. -/
def oddOffsets {A : Type*} [AddCommGroup A] [DecidableEq A] (T : Finset A) (t h : A) (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun e => Odd e ∧ t + e • h ∈ T)

private theorem advance_mod {A : Type*} [AddCommGroup A] (h : A) (i : ℕ) :
    (i % addOrderOf h) • h = i • h := by
  let n := addOrderOf h
  calc
    (i % n) • h = (i % n + (i / n) * n) • h := by
      have hz : ((i / n) * n) • h = 0 := by
        rw [mul_comm, mul_nsmul]
        simp [n]
      rw [add_nsmul, hz, add_zero]
    _ = i • h := by rw [Nat.mul_comm (i / n), Nat.mod_add_div]

/-- For a good orbit, the anchor and its odd partners in the short window
    all consume slots of the original CondA cap. -/
theorem old_good_orbit_offset_cap (B : Arith.Base) (h : B.H) (b : B.H)
    (g : Arith.Loc.Good B h b) (i : ℕ) (hi : i < addOrderOf h)
    (hstart : b + i • h ∈ B.TT) (L : ℕ) (hL : 0 < L)
    (hord : L ≤ addOrderOf h) (hshort : L ≤ B.Ltwo) :
    (oddOffsets B.TT (b + i • h) h L).card + 1 ≤ G.KG B.sc := by
  have ha := g.1 i hi
  let n := addOrderOf h
  let V := oddOffsets B.TT (b + i • h) h L
  let f (e : ℕ) := (i + e) % n
  have h0 : 0 ∉ V := by simp [V, oddOffsets]
  have hinj : Set.InjOn f (insert 0 V : Finset ℕ) := by
    have bound (e : ℕ) (he : e ∈ insert 0 V) : e < n := by
      rcases Finset.mem_insert.mp he with rfl | he
      · exact addOrderOf_pos _
      · exact (Finset.mem_range.mp (Finset.mem_filter.mp he).1).trans_le hord
    intro a ha b hb hab
    have hcong := Nat.ModEq.add_left_cancel' i (show i + a ≡ i + b [MOD n] from hab)
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (bound a ha), Nat.mod_eq_of_lt (bound b hb)] using hcong
  have hs : (insert 0 V).image f ⊆
      (Arith.Loc.topsPos B h b).map Fin.valEmbedding ∩ Formalism.G0.window n i B.Ltwo := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have he' : e < L ∧ b + (i + e) • h ∈ B.TT := by
      rcases Finset.mem_insert.mp he with rfl | he
      · simpa using And.intro hL hstart
      · obtain ⟨hr, _, ht⟩ := Finset.mem_filter.mp he
        exact ⟨Finset.mem_range.mp hr, by simpa [add_nsmul, add_assoc] using ht⟩
    have hx' : f e < n := Nat.mod_lt _ (addOrderOf_pos _)
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · apply Finset.mem_map.mpr
      refine ⟨⟨f e, hx'⟩, ?_, rfl⟩
      simp only [Arith.Loc.topsPos, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [f, n, advance_mod] using he'.2
    · exact Finset.mem_image.mpr ⟨e, Finset.mem_range.mpr (he'.1.trans_le hshort), rfl⟩
  exact (by
    rw [← Finset.card_insert_of_notMem h0, ← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hs).trans ha)


/-- The cap specialization uses the host's literal retained set, prime step,
    and canonical representative. It makes no new selection. -/
theorem actual_host_offset_cap {R : Ranks} (H : Host R) (s : Scale) (p : ℕ)
    (t : R.A) (ht : t ∈ H.TT) (L : ℕ) (hL : 0 < L)
    (hord : L ≤ addOrderOf (hPH H p)) (hshort : L ≤ (baseOf s 0 0 H).Ltwo)
    (g : Arith.Loc.Good (baseOf s 0 0 H) (hPH H p) (Arith.bsH (hPH H p) t)) :
    (oddOffsets H.TT t (hPH H p) L).card + 1 ≤ G.KG s := by
  let h := hPH H p
  let b := Arith.bsH h t
  have greet : ∃ i : ℕ, b + i • h = t := by
    classical
    unfold b Arith.bsH
    split_ifs with he
    · exact Nat.find_spec he
    · exact ⟨0, by simp⟩
  obtain ⟨i, hi⟩ := greet
  have hi' : b + (i % addOrderOf h) • h = t := by simpa only [advance_mod] using hi
  have ht' : b + (i % addOrderOf h) • h ∈ (baseOf s 0 0 H).TT := hi' ▸ ht
  have hc := old_good_orbit_offset_cap (baseOf s 0 0 H) h b g (i % addOrderOf h)
    (Nat.mod_lt _ (addOrderOf_pos _)) ht' L hL hord hshort
  rw [hi'] at hc
  exact hc

/-- There is no such capped orbit for an inert prime with the same anchor
    and two distinct admissible exponents when the short cap is at most two. -/
theorem at_most_one_from_two_slot_cap {S : Finset ℕ} {i j K : ℕ}
    (hS : S.card + 1 ≤ K) (hK : K ≤ 2) (hi : i ∈ S) (hj : j ∈ S) : i = j :=
  (Finset.card_le_one.mp (by omega)) i hi j hj

end
end FrobeniusSpacing

#print axioms FrobeniusSpacing.rank_identity_prime_floor
#print axioms FrobeniusSpacing.no_fixed_rank_val
#print axioms FrobeniusSpacing.inert_step_and_partner
#print axioms FrobeniusSpacing.old_good_orbit_offset_cap
#print axioms FrobeniusSpacing.actual_host_offset_cap
#print axioms FrobeniusSpacing.at_most_one_from_two_slot_cap
