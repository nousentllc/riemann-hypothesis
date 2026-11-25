import RamBase

namespace RamDilate
/-- Rational coefficient precision five equals uniformizer precision ten. -/
theorem contact_sixteen : TargetOne.count 6 (16 : RamBase.R) = 65537 * 2^35 := by
  rw [RamBase.census_six]
  decide +kernel

end RamDilate
#print axioms RamDilate.contact_sixteen
