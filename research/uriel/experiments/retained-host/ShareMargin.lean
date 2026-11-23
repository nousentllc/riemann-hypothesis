import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

noncomputable section

namespace UrielRetained

open Formalism.HC

private theorem count_growth {α : Type*} [DecidableEq α] (U T : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (U.filter p).card ≤ (T.filter p).card + (U \ T).card := by
  have hs : U.filter p ⊆ T.filter p ∪ (U \ T) := by
    intro t ht
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp ht
    by_cases h : t ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu, h⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

/-- With equal retained size, the one-sided difference counts precisely the number of replacements. -/
theorem share_margin {φ : Frame} {T U : Finset φ.A} {a b : ℝ}
    (hT : φ.Shares T a) (size : T.card = U.card)
    (budget : ((U \ T).card : ℝ) ≤ (b - a) * T.card) : φ.Shares U b := by
  classical
  have hc : (T \ U).card = (U \ T).card := by
    have h1 := Finset.card_sdiff_add_card_inter T U
    have h2 := Finset.card_sdiff_add_card_inter U T
    rw [Finset.inter_comm U T] at h2
    omega
  intro γ
  let p := fun t : φ.A => t - γ ∈ φ.A0
  obtain ⟨lo, hi⟩ := abs_le.mp (hT γ)
  have up := count_growth U T p
  have dn := count_growth T U p
  rw [hc] at dn
  have up' : ((U.filter p).card : ℝ) ≤ (T.filter p).card + ((U \ T).card : ℝ) := by exact_mod_cast up
  have dn' : ((T.filter p).card : ℝ) ≤ (U.filter p).card + ((U \ T).card : ℝ) := by exact_mod_cast dn
  change |((U.filter p).card : ℝ) - φ.lam γ * U.card| ≤ b * U.card
  rw [← size, abs_le]
  change -(a * T.card) ≤ ((T.filter p).card : ℝ) - φ.lam γ * T.card at lo
  change ((T.filter p).card : ℝ) - φ.lam γ * T.card ≤ a * T.card at hi
  constructor <;> linarith

/-- On one fixed raw host the retained set occurs in exactly one of the six inputs. -/
theorem replace_for_explicit_formula {Λ : Level} {φ : Frame} {H : HostRaw φ}
    {T U : Finset φ.A} {x eps C : ℝ}
    (h : EAtH Λ H T x eps C) (hs : φ.Shares U (x ^ (-1 + eps))) : EAtH Λ H U x eps C :=
  ⟨h.o_eq, h.kept, h.ps, hs, h.bdG, h.bdL⟩

theorem replace_within_margin {Λ : Level} {φ : Frame} {H : HostRaw φ}
    {T U : Finset φ.A} {x eps C : ℝ}
    (h : EAtH Λ H T x eps C) (hs : φ.Shares T x⁻¹) (size : T.card = U.card)
    (budget : ((U \ T).card : ℝ) ≤ (x ^ (-1 + eps) - x⁻¹) * T.card) : EAtH Λ H U x eps C :=
  replace_for_explicit_formula h (share_margin hs size budget)

#print axioms share_margin
#print axioms replace_within_margin

/-- The size and density inequalities supplied by topsGroup give an explicit lower bound
on the real replacement budget whenever the construction's other hypotheses hold. -/
theorem room_from_size {x eps N m : ℝ} (hx : 1 ≤ x) (he : 0 ≤ eps)
    (ambient : x ^ (2 + 8 * eps) / 2 ≤ N)
    (retained : x ^ (-(eps / 8)) * N / 2 ≤ m) :
    x ^ (1 + 63 * eps / 8) * (x ^ eps - 1) / 4 ≤ (x ^ (-1 + eps) - x⁻¹) * m := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : 0 ≤ x ^ (-(eps / 8)) := (Real.rpow_pos_of_pos hp _).le
  have hxe : 1 ≤ x ^ eps := Real.one_le_rpow hx he
  have hn : x ^ (2 + 63 * eps / 8) / 4 ≤ m := by
    have h := mul_le_mul_of_nonneg_left ambient hpow
    rw [show 2 + 63 * eps / 8 = -(eps / 8) + (2 + 8 * eps) by ring,
      Real.rpow_add hp]
    linarith
  have hrad : x ^ (-1 + eps) - x⁻¹ = x⁻¹ * (x ^ eps - 1) := by
    rw [Real.rpow_add hp, Real.rpow_neg_one]
    ring
  rw [hrad]
  have h := mul_le_mul_of_nonneg_left hn (mul_nonneg (inv_nonneg.mpr hp.le) (sub_nonneg.mpr hxe))
  have eq : x ^ (1 + 63 * eps / 8) = x⁻¹ * x ^ (2 + 63 * eps / 8) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hp]
    congr 1
    ring
  rw [eq]
  linarith

#print axioms room_from_size

end UrielRetained
