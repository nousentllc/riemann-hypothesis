import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Uriel.ExceptionalGeometry

/-- The clean window can include its right endpoint. The excluded band includes
its left endpoint and excludes its right endpoint. -/
theorem hit_iff {L B a y : ℝ} (hL : 1 ≤ L) (hB : 1 < B)
    (ha : 0 < a) (hy : 0 ≤ y) :
    (∃ u : ℝ, y ≤ u ∧ u ≤ L*y ∧ a ≤ u ∧ u < B*a) ↔ a ≤ L*y ∧ y < B*a := by
  constructor
  · rintro ⟨u, h1, h2, h3, h4⟩
    exact ⟨h3.trans h2, h1.trans_lt h4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨max y a, le_max_left _ _, max_le ?_ h1, le_max_right _ _, max_lt h2 ?_⟩
    · exact le_mul_of_one_le_left hy hL
    · simpa using mul_lt_mul_of_pos_right hB ha

/-- The uniform sufficient budget on the logarithmic scale, at arbitrary
positive power width L-1. The argument uses a single set of centers throughout. -/
theorem clean_budget (R : ℕ) (L B U : ℝ) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hU : 0 < U) (T : Finset ℝ) (hT : T.card ≤ R) :
    ∃ y : ℝ, U / (L*(L*B)^R) ≤ y ∧ L*y ≤ U ∧
       ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ L*y → a ≤ u → B*a ≤ u := by
  classical
  have hLp : 0 < L := by linarith
  have hBp : 0 < B := by linarith
  have hprod : 1 ≤ L*B := one_le_mul_of_one_le_of_one_le hL hB
  have hprodpos : 0 < L*B := mul_pos hLp hBp
  induction R generalizing U T with
  | zero =>
    have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨U/L, by simp, by field_simp; norm_num, ?_⟩
    simp [he]
  | succ n ih =>
    by_cases h : ∃ a ∈ T, U/(L*B) < a ∧ a ≤ U
    · obtain ⟨a, ha, hlo, _⟩ := h
      obtain ⟨y, h1, h2, h3⟩ := ih (U/(L*B)) (div_pos hU hprodpos) (T.erase a)
        (by rw [Finset.card_erase_of_mem ha]; omega)
      refine ⟨y, ?_, h2.trans (div_le_self hU.le hprod), ?_⟩
      · calc
          U / (L * (L*B) ^ (n+1)) = U/(L*B) / (L*(L*B)^n) := by
            rw [div_div, pow_succ]; ring
          _ ≤ y := h1
      · intro a' ha' u hu1 hu2 hau
        by_cases heq : a' = a
        · subst a'
          exact False.elim (not_lt_of_ge (hau.trans (hu2.trans h2)) hlo)
        · exact h3 a' (Finset.mem_erase.mpr ⟨heq, ha'⟩) u hu1 hu2 hau
    · push Not at h
      refine ⟨U/L, ?_, by field_simp; norm_num, ?_⟩
      · apply div_le_div_of_nonneg_left hU.le hLp
        exact le_mul_of_one_le_right hLp.le (one_le_pow₀ hprod)
      · intro a ha u hu1 hu2 hau
        have htop : L * (U/L) = U := by field_simp
        have hb := h a ha
        by_contra! hn
        have : U/(L*B) < a := by
          apply (div_lt_iff₀ hprodpos).2
          have hu' : U < B * a * L := (div_lt_iff₀ hLp).1 (hu1.trans_lt hn)
          linarith only [show B*a*L = a*(L*B) by ring, hu']
        exact ((not_lt_of_ge ((hau.trans hu2).trans htop.le)) (hb this))

/-- A positive length k fits in the intersection precisely when four endpoint
comparisons hold. This is the algebra behind the one-band minimax formula. -/
theorem overlap_at_least {L B t k : ℝ} (hk : 0 < k) :
    k ≤ max 0 (min L (B*t) - max 1 t) ↔
      k ≤ L-1 ∧ k ≤ L-t ∧ k ≤ B*t-1 ∧ k ≤ B*t-t := by
  rw [le_max_iff, or_iff_right (not_le_of_gt hk)]
  constructor
  · intro h
    have h1 := min_le_left L (B*t)
    have h2 := min_le_right L (B*t)
    have h3 := le_max_left (1:ℝ) t
    have h4 := le_max_right (1:ℝ) t
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hm1 : max 1 t ≤ L-k := max_le (by linarith) (by linarith)
    have hm2 : max 1 t ≤ B*t-k := max_le (by linarith) (by linarith)
    have hm : max 1 t + k ≤ min L (B*t) := le_min (by linarith) (by linarith)
    linarith

/-- Find a cell of a finite geometric progression containing v. -/
private theorem chain_index {s t v : ℝ} (R : ℕ) (hl : s ≤ v) (hh : v < s*t^R) :
    ∃ j < R, s*t^j ≤ v ∧ v < s*t^(j+1) := by
  induction R with
  | zero => simp at hh; linarith
  | succ n ih =>
    by_cases h : v < s*t^n
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, Nat.lt_succ_self _, le_of_not_gt h, hh⟩

/-- A geometric chain of exceptional centers hits every admitted start
v in the stated open search range. This is the adversarial part of the
sharpness construction; selecting its slack is an elementary real step. -/
theorem chain_hits {s t v L B : ℝ} (R : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hL : 1 ≤ L) (hB : 1 < B) (hstep : t ≤ L*B) (hv : s ≤ v)
    (htop : v < s*t^R) :
    ∃ j < R, ∃ u : ℝ, v ≤ u ∧ u ≤ L*v ∧ L*(s*t^j) ≤ u ∧ u < B*(L*(s*t^j)) := by
  obtain ⟨j, hj, hlo, hhi⟩ := chain_index R hv htop
  have hp : 0 < s*t^j := by positivity
  have hLp : 0 < L := by linarith
  refine ⟨j, hj, (hit_iff hL hB (mul_pos hLp hp) (hs.le.trans hv)).2 ⟨?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_left hlo hLp.le
  · calc
      v < s*t^j*t := by simpa [pow_succ, mul_assoc] using hhi
      _ ≤ s*t^j*(L*B) := mul_le_mul_of_nonneg_left hstep hp.le
      _ = B*(L*(s*t^j)) := by ring

/-- Complete positive superlevel characterization of the one-band minimax
fraction, expressed in units of the starting log ordinate. Dividing k by
L-1 gives the fraction. -/
theorem one_band_capacity {L B r k : ℝ} (hB : 1 < B) (hr : 1 ≤ r) (hk : 0 < k) :
    (∃ a : ℝ, 0 < a ∧ ∀ v ∈ Set.Icc (1 : ℝ) r,
      k ≤ max 0 (min L (B*(a/v)) - max 1 (a/v))) ↔
       k ≤ L-1 ∧ (B+r)*k ≤ B*L-r ∧ (r+B-1)*k ≤ L*(B-1) := by
  have hrp : 0 < r := by linarith
  have hb : 0 ≤ B := by linarith
  have hb1 : 0 ≤ B-1 := by linarith
  constructor
  · rintro ⟨a, _, ha⟩
    have hfirst := (overlap_at_least hk).1 (ha 1 ⟨le_rfl, hr⟩)
    simp only [div_one] at hfirst
    have hlast := (overlap_at_least hk).1 (ha r ⟨hr, le_rfl⟩)
    have hupper : a ≤ L-k := by linarith [hfirst.2.1]
    have hlow1 : (1+k)*r ≤ B*a := by
      apply (le_div_iff₀ hrp).1
      rw [mul_div_assoc]
      linarith [hlast.2.2.1]
    have hlow2 : k*r ≤ (B-1)*a := by
      apply (le_div_iff₀ hrp).1
      rw [mul_div_assoc, sub_mul, one_mul]
      exact hlast.2.2.2
    refine ⟨hfirst.1, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hupper hb]
    · nlinarith [mul_le_mul_of_nonneg_left hupper hb1]
  · rintro ⟨hwidth,h1,h2⟩
    have ha : 0 < L-k := by linarith
    refine ⟨L-k,ha,?_⟩
    intro v hv
    have hvp : 0 < v := lt_of_lt_of_le zero_lt_one hv.1
    have hupper : (L-k)/v ≤ L-k := div_le_self ha.le hv.1
    have hlow1 : 1+k ≤ B*((L-k)/v) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hvp).2
      have hc := mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ 1+k by linarith)
      nlinarith
    have hlow2 : k ≤ (B-1)*((L-k)/v) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hvp).2
      have hc := mul_le_mul_of_nonneg_left hv.2 hk.le
      nlinarith
    apply (overlap_at_least hk).2
    refine ⟨hwidth,by linarith,by linarith,?_⟩
    simpa only [sub_mul,one_mul] using hlow2

#print axioms hit_iff
#print axioms clean_budget
#print axioms overlap_at_least
#print axioms chain_hits
#print axioms one_band_capacity
end Uriel.ExceptionalGeometry
