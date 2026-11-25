import DilateDefs
import RamLift

/-! Above the fifth uniformizer digit, an odd companion multiplier is already
a square of a unit.  This includes every 1 + 2^q π with q ≥ 2 and only needs
a finite quotient. -/
noncomputable section
namespace RamDilate

theorem deep_companion_square (r q : ℕ) (hq : 2 ≤ q) :
    ∃ u : (S r)ˣ, (u:S r)^2 = 1 + (2:S r)^q * QuadraticAlgebra.omega := by
  let π : S r := QuadraticAlgebra.omega
  have hp : π^2=2 := by rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]; rfl
  have hπ : IsNilpotent π := by
    have h : (2:ZMod (2^r))^r = 0 := by exact_mod_cast ZMod.natCast_self (2^r)
    have h' := congrArg (algebraMap (ZMod (2^r)) (S r)) h
    exact ⟨2*r,by rw [pow_mul,hp]; simpa only [map_pow,map_ofNat,map_zero] using h'⟩
  let : Fintype (S r) := Fintype.ofEquiv _ (QuadraticAlgebra.equivProd _ _).symm
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨y,hy⟩ := RamBase.five_digit_pivot π hπ hp 1 ((2:S r)^j)
  have hnil := (Commute.all π (π^2*y)).isNilpotent_mul_right hπ
  have hu : IsUnit (1+π^3*y) := by
    convert hnil.isUnit_one_add using 1; ring
  refine ⟨hu.unit,?_⟩
  rw [hu.unit_spec]
  simp only [Units.val_one,one_pow] at hy
  rw [hy]
  have hp5 : π^5=4*π := by linear_combination (π*(π^2+2))*hp
  change 1+π^5*2^j = 1+2^(2+j)*π
  rw [hp5,pow_add]
  ring

/-- Multiplication of every coordinate by the chosen unit sends the entire
six-square fiber to the fiber over its square multiple. -/
theorem deep_companion_count (r q : ℕ) (hq : 2 ≤ q) (s : S r) :
    TargetOne.count 6 (s*(1+(2:S r)^q*QuadraticAlgebra.omega)) =
      TargetOne.count 6 s := by
  obtain ⟨u,hu⟩ := deep_companion_square r q hq
  rw [← hu,mul_comm, TargetFour.scaled]
end RamDilate
#print axioms RamDilate.deep_companion_count
