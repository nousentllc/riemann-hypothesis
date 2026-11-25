import Mathlib

/-! The scalar comparison used by rank-one Siegel–Weil normalization.
The allowed positive integers and their finite-place product are explicit parameters. -/
namespace GrowthConsumer

/-- At positive allowed integers, the lower profile exceeds every fixed multiple
of the analytic error's power. -/
def RelativeGrowth (allowed : ℕ → Prop) (P : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ B : ℝ, ∃ a : ℕ, 0 < a ∧ allowed a ∧ B * (a : ℝ)^q < P a

/-- The matched scalar inequality identifies the multiplier for every finite error constant. -/
def ForcesOne (allowed : ℕ → Prop) (P : ℕ → ℝ) (q : ℕ) (w : ℝ) : Prop :=
  ∀ c C : ℝ, (∀ a : ℕ, 0 < a → allowed a →
    |c-1| * (w * P a) ≤ C * (a : ℝ)^q) → c = 1

/-- Exact criterion at the level of real inequalities. If the relative growth fails,
the multiplier 2 and a finite error constant already give a counterexample. -/
theorem forces_iff_relativeGrowth {allowed : ℕ → Prop} {P : ℕ → ℝ} {q : ℕ}
    {w : ℝ} (hw : 0 < w) : ForcesOne allowed P q w ↔ RelativeGrowth allowed P q := by
  constructor
  · intro force
    unfold RelativeGrowth
    by_contra bad
    push Not at bad
    obtain ⟨B, hB⟩ := bad
    have absurd := force 2 (w * B) (by
      intro a ha haS
      have h := mul_le_mul_of_nonneg_left (hB a ha haS) hw.le
      norm_num [mul_assoc] at h ⊢
      exact h)
    norm_num at absurd
  · intro growth c C hbound
    by_contra hc
    let d := |c - 1| * w
    have hd : 0 < d := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hc)) hw
    obtain ⟨a, ha, hs, h⟩ := growth (C/d)
    have impossible : C * (a : ℝ)^q < |c-1| * (w * P a) := calc
      C * (a : ℝ)^q = d * ((C/d) * (a : ℝ)^q) := by field_simp
      _ < d * P a := mul_lt_mul_of_pos_left h hd
      _ = |c-1| * (w * P a) := by dsimp [d]; ring
    exact (not_lt_of_ge (hbound a ha hs)) impossible

/-- The source supplies a stronger cofinal lower power on a common allowed set. -/
theorem relativeGrowth_of_power_gap {allowed : ℕ → Prop} {P : ℕ → ℝ} {p q : ℕ}
    {κ : ℝ} (hκ : 0 < κ) (hgap : q < p)
    (lower : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ allowed a ∧ κ * (a : ℝ)^p ≤ P a) :
    RelativeGrowth allowed P q := by
  intro B
  obtain ⟨k, hk⟩ := exists_nat_gt (B/κ)
  obtain ⟨a, ha, hs, hP⟩ := lower k
  have hapos : 0 < a := lt_of_le_of_lt (Nat.zero_le _) ha
  have har : 1 ≤ (a : ℝ) := by exact_mod_cast hapos
  have hak : (k : ℝ) < a := by exact_mod_cast ha
  have hk' : B < (a : ℝ) * κ := (div_lt_iff₀ hκ).mp (hk.trans hak)
  refine ⟨a,hapos,hs,?_⟩
  calc B * (a : ℝ)^q < (a * κ) * (a : ℝ)^q :=
         mul_lt_mul_of_pos_right hk' (pow_pos (by linarith) _)
       _ = κ * (a : ℝ)^(q+1) := by rw [pow_succ]; ring
       _ ≤ κ * (a : ℝ)^p :=
         mul_le_mul_of_nonneg_left (pow_le_pow_right₀ har hgap) hκ.le
       _ ≤ P a := hP

/-- Rank and field degree specialize the algebraic gap to the exponents in sw_one. -/
theorem rank_gap (D M : ℕ) (hD : 0 < D) (hM : 3 ≤ M) : D*M < D*(2*M-2) :=
  Nat.mul_lt_mul_of_pos_left (by omega) hD

/-- The actual real scalar interface after the Euler integral identification at each
chosen dilation. The finite product and the analytic discrepancy use the same a. -/
theorem rank_one_comparison {D M : ℕ} (hD : 0 < D) (hM : 3 ≤ M)
    {c : NNReal} {w : ENNReal} (hw : 0 < w.toReal) {κ C : ℝ} (hκ : 0 < κ)
    (P : ℕ → ℝ)
    (lower : ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ)^(D*(2*M-2)) ≤ P a)
    (upper : ∀ a : ℕ, 0 < a → 0 ≤ P a → ∃ I : ℝ,
      I = (c : ℝ)*w.toReal*P a ∧ |I-w.toReal*P a| ≤ C*(a : ℝ)^(D*M)) : c=1 := by
  let S : ℕ → Prop := fun a => 0 ≤ P a
  have growth : RelativeGrowth S P (D*M) := relativeGrowth_of_power_gap hκ (rank_gap D M hD hM)
    (fun k => by
      obtain ⟨a,ha,hP⟩ := lower k
      exact ⟨a,ha,(show 0 ≤ κ*(a : ℝ)^(D*(2*M-2)) by positivity).trans hP,hP⟩)
  have forces := (forces_iff_relativeGrowth hw).mpr growth
  have heq := forces (c : ℝ) C (by
    intro a ha haS
    obtain ⟨I,rfl,hI⟩ := upper a ha haS
    have hnonneg : 0 ≤ w.toReal * P a := mul_nonneg hw.le haS
    rw [show (c : ℝ)*w.toReal*P a - w.toReal*P a = ((c : ℝ)-1)*(w.toReal*P a) by ring,
      abs_mul, abs_of_nonneg hnonneg] at hI
    exact hI)
  exact_mod_cast heq

/-- With a nonpositive exponent gap, the admissible multiplier 2 obeys both bounds
at every positive integer in the unit-weight model. -/
theorem boundary_countermodel (p q : ℕ) (hpq : p ≤ q) :
    (∀ k : ℕ, ∃ a : ℕ, k<a ∧ 1 * (a : ℝ)^p ≤ (a : ℝ)^p) ∧
    (∀ a : ℕ, 0<a → |(2:ℝ)-1| * (1 * (a : ℝ)^p) ≤ 1*(a : ℝ)^q) ∧ (2:ℝ) ≠ 1 := by
  refine ⟨fun k => ⟨k+1, by omega, by simp⟩, ?_, by norm_num⟩
  intro a ha
  have h : (1:ℝ) ≤ a := by exact_mod_cast ha
  norm_num
  exact pow_le_pow_right₀ h hpq

/-- A linear lower witness on evens and a bounded upper witness on odds give no
information about a shared multiplier. -/
theorem unmatched_countermodel :
    ∃ P : ℕ → ℝ,
      (∀ k : ℕ, ∃ a : ℕ, k<a ∧ (a : ℝ) ≤ P a) ∧
      (∀ k : ℕ, ∃ a : ℕ, k<a ∧ |(2:ℝ)-1| * (1 * P a) ≤ 1) ∧ (2:ℝ) ≠ 1 := by
  let P : ℕ → ℝ := fun a => if a % 2 = 0 then (a : ℝ) else 0
  refine ⟨P, ?_, ?_, by norm_num⟩
  · intro k
    refine ⟨2*(k+1),by omega,?_⟩
    simp [P]
  · intro k
    refine ⟨2*(k+1)+1,by omega,?_⟩
    simp [P]

end GrowthConsumer
#print axioms GrowthConsumer.forces_iff_relativeGrowth
#print axioms GrowthConsumer.relativeGrowth_of_power_gap
#print axioms GrowthConsumer.rank_one_comparison
#print axioms GrowthConsumer.boundary_countermodel
#print axioms GrowthConsumer.unmatched_countermodel
