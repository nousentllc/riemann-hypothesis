import DilateLow

open TargetOne
noncomputable section
namespace RamDilate

theorem low3_four_companion : count 6 ((4 : RamField.R 3) * (1 + QuadraticAlgebra.omega)) = 2139095040 := by
  let : Fintype (RamField.R 3) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 8 4) 16 (RamLift.scalar_count 8 4) ((4 : RamField.R 3) * (1 + QuadraticAlgebra.omega))
  have e : projectedTotal (RamLift.reduce 8 4) ((4 : RamField.R 3) * (1 + QuadraticAlgebra.omega)) = 35888059530608640 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

theorem low4_eight_companion : count 6 ((8 : RamField.R 4) * (1 + QuadraticAlgebra.omega)) = 2198486384640 := by
  let : Fintype (RamField.R 4) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  have h := project_total (RamLift.reduce 16 2) 4 (RamLift.scalar_count 16 2) ((8 : RamField.R 4) * (1 + QuadraticAlgebra.omega))
  have e : projectedTotal (RamLift.reduce 16 2) ((8 : RamField.R 4) * (1 + QuadraticAlgebra.omega)) = 9005000231485440 := by decide +kernel
  exact Nat.eq_of_mul_eq_mul_right (by decide) (h.trans e)

end RamDilate
#print axioms RamDilate.low3_four_companion
#print axioms RamDilate.low4_eight_companion
