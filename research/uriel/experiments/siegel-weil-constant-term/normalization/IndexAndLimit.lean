import Mathlib
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
namespace GlobalTheory.CompanionTheory.RgBaseCnt
theorem limit_cancel {κ : ℝ≥0} {pc vol V L : ℝ≥0∞} {P a b : ℝ → ℝ≥0∞}
    (h0 : pc ≠ 0) (h1 : pc ≠ ⊤) (hv0 : vol ≠ 0) (hvt : vol ≠ ⊤) (hV0 : V ≠ 0) (hVt : V ≠ ⊤)
    (hP : Tendsto P (𝓝[>] 1) (𝓝 (L * pc)))
    (hLt : L ≠ ⊤)
    (hA : Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * ((κ : ℝ≥0∞) * a s)) (𝓝[>] 1) (𝓝 (vol * V / 2)))
    (hB : Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * b s) (𝓝[>] 1) (𝓝 (pc * vol * V)))
    (hR : ∀ s : ℝ, 1 < s → P s * a s = b s) : L / 2 = κ := by
  have hW0 : vol * V ≠ 0 := mul_ne_zero hv0 hV0
  have hWt : vol * V ≠ ⊤ := ENNReal.mul_ne_top hvt hVt
  have hLp : L * pc ≠ ⊤ := ENNReal.mul_ne_top hLt h1
  have hWh : vol * V / 2 ≠ ⊤ := ENNReal.div_ne_top hWt (by norm_num)
  have e1 := ENNReal.Tendsto.mul hP (Or.inr hWh) hA (Or.inr hLp)
  have e2 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hB (Or.inr ENNReal.coe_ne_top)
  have e3 : (L * pc) * (vol * V / 2) = (κ : ℝ≥0∞) * (pc * vol * V) := by
    refine tendsto_nhds_unique e1 (e2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← hR s hs]
    ring
  have hpw : pc * (vol * V) ≠ 0 := mul_ne_zero h0 hW0
  have hpwt : pc * (vol * V) ≠ ⊤ := ENNReal.mul_ne_top h1 hWt
  have e4 : (L / 2) * (pc * (vol * V)) = (κ : ℝ≥0∞) * (pc * (vol * V)) := by
    rw [mul_assoc pc vol V] at e3
    rw [← e3, div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact (ENNReal.mul_left_inj hpw hpwt).1 e4

#print axioms limit_cancel
end GlobalTheory.CompanionTheory.RgBaseCnt
namespace SWCheck

/-- Group-theoretic part of hEx, with the nontrivial character supplied. -/
theorem norm_kernel_index {G : Type*} [Group G] (χ : G →* ℤˣ)
    (h : ∃ b, χ b ≠ 1) : χ.ker.index = 2 := by
  obtain ⟨b, hb⟩ := h
  have hr : χ.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
  rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- Control: the codomain by itself does not force index two. -/
theorem trivial_index {G : Type*} [Group G] :
    (1 : G →* ℤˣ).ker.index = 1 := by simp

#print axioms norm_kernel_index
#print axioms trivial_index
end SWCheck
end
