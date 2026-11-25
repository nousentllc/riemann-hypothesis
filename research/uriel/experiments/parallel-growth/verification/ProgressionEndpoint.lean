import ProgressionGeometry
import ProgressionGrowth
import RankOneConsumer

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
open NumberField IsDedekindDomain MeasureTheory
noncomputable section
namespace ProgressionEndpoint

/-- Supply the actual finite-place input of the original rank-one comparison
with a uniformly spaced sequence. The comparison asks only for cofinality. -/
theorem provider : GrowthConsumer.RankOneGrowthProvider := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b lam hlam m hm β hβ hne
  obtain ⟨N,Q,hN,hQ,c,hc,hl⟩ := ProgressionGrowth.progression_growth (b := b)
    hσ hJ hM hlam hm β hβ hne
  refine ⟨c,hc,fun k => ?_⟩
  obtain ⟨a,ha,_,hp⟩ := ProgressionGeometry.from_progression hQ hN
    (P := fun a => c*(a:ℝ)^(Module.finrank ℚ F*(2*M-2)) ≤ GrowthConsumer.finiteProduct σ b m β a) hl k
  exact ⟨a,ha,hp⟩

theorem sw_one_via_progression : GrowthConsumer.RankOneConclusion :=
  GrowthConsumer.sw_one_of_growth provider

end ProgressionEndpoint
#print axioms ProgressionEndpoint.provider
#print axioms ProgressionEndpoint.sw_one_via_progression
