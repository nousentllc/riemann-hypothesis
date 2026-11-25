import Mathlib
namespace RamBase
/-- The change in an odd square after shifting its last digits.  Only π² = 2
is used to locate the first freely changeable target digit. -/
theorem five_digit_identity {A : Type*} [CommRing A] (π u y : A) (hπ : π^2 = 2) :
    (u+π^3*y)^2 = u^2+π^5*(u*y+π*y^2) := by
  linear_combination -(π^3*u*y)*(hπ)

/-- Over every finite quotient where π is nilpotent, an invertible pivot
gives a permutation of the remaining digits. -/
theorem pivot_permutation {A : Type*} [CommRing A] [Finite A] (π : A)
    (hp : IsNilpotent π) (u : Aˣ) :
    Function.Bijective (fun y : A => (u:A)*y+π*y^2) := by
  have inj : Function.Injective (fun y : A => (u:A)*y+π*y^2) := by
    intro x y h
    have hnu : IsNilpotent (π*((↑(u⁻¹) : A)*(x+y))) := (Commute.all ..).isNilpotent_mul_right hp
    have hu : IsUnit ((u:A)+π*(x+y)) := by
      convert u.isUnit.mul hnu.isUnit_one_add using 1
      have hi : (u:A) * (↑(u⁻¹):A) = 1 := u.mul_inv
      linear_combination -(π*(x+y))*hi
    apply hu.mul_left_cancel
    linear_combination h
  exact ⟨inj,Finite.surjective_of_injective inj⟩

theorem five_digit_pivot {A : Type*} [CommRing A] [Finite A] (π : A)
    (hp : IsNilpotent π) (hπ : π^2=2) (u : Aˣ) (w : A) :
    ∃ y : A, ((u:A)+π^3*y)^2 = (u:A)^2+π^5*w := by
  obtain ⟨y,hy⟩ := (pivot_permutation π hp u).2 w
  exact ⟨y,(five_digit_identity π (u:A) y hπ).trans (by rw [← hy])⟩
end RamBase
#print axioms RamBase.five_digit_pivot
