import RankOneConsumer
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConvergesStatement

namespace GrowthConsumer

/-- End-to-end comparison using the original public rank-one growth theorem. -/
theorem sw_one_via_pinned_growth : RankOneConclusion :=
  sw_one_of_growth GlobalTheory.T.exists_frequently_mul_pow_le_tprod_rank_one_local_density

end GrowthConsumer
#print axioms GrowthConsumer.sw_one_via_pinned_growth
