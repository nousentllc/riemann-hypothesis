import Mathlib

open Matrix
noncomputable section
namespace ReadableBoxParameters
variable {K : Type} [Field K] [CharZero K]

/-- A fractional box in the two scalar coordinates of the Gaussian algebra. -/
def box (S : Subring K) (w : K) (x y : K) : Prop :=
  ∃ a b : S, x=w*(a:K) ∧ y=w*(b:K)

theorem axis (S : Subring K) (h a : K) (k : S) :
    box S h (h*(k:K)) a ↔ ∃ t : S, a=h*(t:K) := by
  constructor
  · rintro ⟨_,b,_,hb⟩; exact ⟨b,hb⟩
  · rintro ⟨t,rfl⟩; exact ⟨k,t,rfl,rfl⟩

/-- Multiplication by an integral Gaussian unit preserves every scalar box. -/
theorem rotate (S : Subring K) (u v : S) (N : Sˣ)
    (hN : (u:K)^2+(v:K)^2=(N.val:K)) (w x y : K) :
    box S w ((u:K)*x-(v:K)*y) ((v:K)*x+(u:K)*y) ↔ box S w x y := by
  have hinv : ((N⁻¹).val:K)*(N.val:K)=1 := by exact_mod_cast N.inv_mul
  constructor
  · rintro ⟨f,g,hf,hg⟩
    refine ⟨(N⁻¹).val*(u*f+v*g),(N⁻¹).val*(-v*f+u*g),?_,?_⟩
    all_goals push_cast
    · linear_combination ((N⁻¹).val:K)*(u:K)*hf + ((N⁻¹).val:K)*(v:K)*hg -
        ((N⁻¹).val:K)*x*hN - x*hinv
    · linear_combination -((N⁻¹).val:K)*(v:K)*hf + ((N⁻¹).val:K)*(u:K)*hg -
        ((N⁻¹).val:K)*y*hN - y*hinv
  · rintro ⟨f,g,rfl,rfl⟩
    refine ⟨u*f-v*g,v*f+u*g,?_,?_⟩ <;> push_cast <;> ring

/-- With pivot p=2U and offset b=p(r+i a), b fits a box of width 2h
exactly when the free skew coefficient fits a box of width h, once r=h k. -/
theorem offset_box (S : Subring K) (u v : S) (N : Sˣ)
    (hN : (u:K)^2+(v:K)^2=(N.val:K)) (h a : K) (k : S) :
    box S (2*h) (2*((u:K)*(h*k)-(v:K)*a)) (2*((v:K)*(h*k)+(u:K)*a)) ↔
    ∃ t : S, a=h*(t:K) := by
  have scale (x y : K) : box S (2*h) (2*x) (2*y) ↔ box S h x y := by
    constructor <;> rintro ⟨f,g,hf,hg⟩ <;> refine ⟨f,g,?_,?_⟩
    · linear_combination hf/2
    · linear_combination hg/2
    · linear_combination 2*hf
    · linear_combination 2*hg
  rw [scale,rotate S u v N hN,axis S h a k]

/-- Width 4d, pivot 2+4d(A+iB), residual 4d(L+iM), target 4+16d t.
The real coefficient of b/p is 2d times an integral expression when N is a unit. -/
theorem real_offset (d A B L M t N : K)
    (hN : N = (1+2*d*A)^2+(2*d*B)^2) (hne : N ≠ 0) :
    ((4+16*d*t)+((4*d*L)^2+(4*d*M)^2)-
      ((2+4*d*A)^2+(4*d*B)^2)) / (2*((2+4*d*A)^2+(4*d*B)^2)) =
      2*d*((t-A+d*(L^2+M^2-A^2-B^2))/N) := by
  have he : (2+4*d*A)^2+(4*d*B)^2 = 4*N := by rw [hN]; ring
  rw [he]; field_simp; rw [hN]; ring

/-- The block sending (b,v) to the last two physical Gaussian components
has determinant one. Its inverse therefore also has integral coefficients. -/
theorem bottom_inverse {R : Type*} [CommRing R] (B D E F b v : R)
    (h : B*E+D*F = -1) :
    (-E)*(B*b+F*v)-F*(D*b-E*v)=b ∧
    (-D)*(B*b+F*v)+B*(D*b-E*v)=v := by
  constructor <;> first | linear_combination -b*h | linear_combination -v*h

theorem width_ratio (m : ℕ) (hm : 1 ≤ m) :
    2*(1/4:ℚ)^(2*m)*(1/4)^(2*m)*(1/4)^(m-1) = 8*(1/4)^(5*m) := by
  rw [show 5*m = (2*m+2*m+(m-1))+1 by omega, pow_succ,
    pow_add (1/4:ℚ) (2*m+2*m) (m-1), pow_add (1/4:ℚ) (2*m) (2*m)]
  ring

end ReadableBoxParameters
#print axioms ReadableBoxParameters.offset_box
#print axioms ReadableBoxParameters.real_offset
#print axioms ReadableBoxParameters.bottom_inverse
#print axioms ReadableBoxParameters.width_ratio
