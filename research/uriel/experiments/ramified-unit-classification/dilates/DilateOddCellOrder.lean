import DilateOddCellCore
import RamFieldMeasure

/-! The odd congruence in the finite count is also the genuine principal
ideal congruence in the completed coefficient order. -/
noncomputable section
namespace RamDilate.OddCell
open RamField

private theorem digit_pi (r : ℕ) : digit r (pi : O) = (pi : S r) := by
  apply QuadraticAlgebra.ext
  · exact map_zero _
  · exact map_one _

private theorem kernel_dvd (r : ℕ) (x : O) (hx : digit r x=0) : (2:O)^r ∣ x := by
  have one (z : ℤ_[2]) (h : PadicInt.toZModPow r z=0) : (2:ℤ_[2])^r ∣ z := by
    change z ∈ RingHom.ker (PadicInt.toZModPow r) at h
    rwa [PadicInt.ker_toZModPow,Ideal.mem_span_singleton] at h
  obtain ⟨a,ha⟩ := one x.re (congrArg QuadraticAlgebra.re hx)
  obtain ⟨b,hb⟩ := one x.im (congrArg QuadraticAlgebra.im hx)
  refine ⟨⟨a,b⟩,?_⟩
  have hsp : (2:O)^r=((2^r:ℕ):O) := by simp
  rw [hsp]
  apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,QuadraticAlgebra.re_natCast,QuadraticAlgebra.im_natCast] <;> simp [ha,hb]

/-- Reduction modulo the next full coefficient digit detects divisibility by
π^(2r+1) in O, including its converse; no lift from a finite solution is assumed. -/
theorem odd_dvd_iff (r : ℕ) (x : O) :
    (pi:O)^(2*r+1) ∣ x ↔ (pi:S (r+1))^(2*r+1) ∣ digit (r+1) x := by
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨digit (r+1) w,by rw [map_mul,map_pow,digit_pi]⟩
  · rintro ⟨t,ht⟩
    obtain ⟨w,hw⟩ := digit_surjective (r+1) t
    have hz : digit (r+1) (x-pi^(2*r+1)*w)=0 := by
      rw [map_sub,map_mul,map_pow,digit_pi,hw,ht,sub_self]
    have hd : (pi:O)^(2*r+1) ∣ (2:O)^(r+1) := by
      refine ⟨pi,?_⟩
      rw [←pi_sq,←pow_mul,←pow_succ]
      congr 1
    obtain ⟨c,hc⟩ := dvd_trans hd (kernel_dvd (r+1) _ hz)
    refine ⟨c+w,?_⟩
    linear_combination hc

theorem order_children (r : ℕ) (x : O) :
    (pi:O)^(2*r+1) ∣ x-2^r ↔
      digit (r+1) x = center r ∨ digit (r+1) x = center r*(1+pi) := by
  rw [odd_dvd_iff,map_sub,map_pow,map_ofNat]
  simpa only [center,Nat.cast_pow,Nat.cast_ofNat] using children r (digit (r+1) x)

/-- The odd ball is defined by divisibility in O, then included in K. -/
def oddCylinder (r : ℕ) : Set K := inc '' {x : O | (pi:O)^(2*r+1) ∣ x-2^r}

theorem cylinder_children (r : ℕ) : oddCylinder r =
    cylinder (r+1) (center r) ∪ cylinder (r+1) (center r*(1+pi)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    rcases (order_children r z).mp hz with h|h
    · exact Or.inl ⟨z,h,rfl⟩
    · exact Or.inr ⟨z,h,rfl⟩
  · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
    · exact ⟨z,(order_children r z).mpr (Or.inl hz),rfl⟩
    · exact ⟨z,(order_children r z).mpr (Or.inr hz),rfl⟩

theorem disjoint_children (r : ℕ) : Disjoint (cylinder (r+1) (center r))
    (cylinder (r+1) (center r*(1+pi))) := disjoint_cyl _ (distinct _)

end RamDilate.OddCell
#print axioms RamDilate.OddCell.cylinder_children
