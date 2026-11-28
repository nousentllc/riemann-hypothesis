import UrielFragments

namespace UrielExperiment

/-- Bundle the scalar hypotheses of the source's numeric lemma and allow its coefficient to vary. -/
def SlopeCoefficient (C : ℝ) : Prop :=
  ∀ dg db μ μg m lg δ Q : ℝ, 0 < dg + db → 0 ≤ dg → 0 ≤ db →
    (dg + db) * μ ≤ dg * μg + db * (m + lg) → 0 ≤ δ → δ ≤ 1 / 12 →
    db ≤ 3 * δ * (dg + db) → m ≤ Q → -Q ≤ μ → lg ≤ Q → 0 ≤ lg →
    μ - C * δ * Q ≤ μg

theorem slopeCoefficient_ge_twelve (C : ℝ) (h : SlopeCoefficient C) : 12 ≤ C := by
  have hbound := h 3 1 (-1) (-2) 1 1 (1/12) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem slopeCoefficient_iff (C : ℝ) : SlopeCoefficient C ↔ 12 ≤ C := by
  refine ⟨slopeCoefficient_ge_twelve C, ?_⟩
  intro hC dg db μ μg m lg δ Q hd hg hb hc hδ hδ' hr hm hμ hlg hlg0
  have hQ : 0 ≤ Q := hlg0.trans hlg
  have hbase := GlobalTheory.CutNum.numeric hd hg hb hc hδ hδ' hr hm hμ hlg hlg0
  have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hδ) hQ
  linarith

end UrielExperiment
